"""
CPLEX MSxLSPSC/MS04 matheuristic for P3SAML3P.

This file is intentionally separate from CPLEX_ILP.py.

CPLEX_ILP.py remains the exact Eq. (2)-(12) reproduction. This file implements
a Section 4 MSxLSPSC/MS04-style matheuristic: decoder D1, neighborhood N2, and
stopping rule S2.
"""

import argparse
import csv
import math
import os
import random
import time as time_module
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional, Sequence, Tuple

from docplex.mp.model import Model


PROJECT_ROOT = Path(__file__).resolve().parent.parent
DATA_DIR = PROJECT_ROOT / "presedent_graph"
POWER_DIR = PROJECT_ROOT / "official_task_power"
DEFAULT_OUTPUT_ROOT = PROJECT_ROOT / "Output" / Path(__file__).stem
OUTPUT_ROOT = Path(os.environ.get("OUTPUT_ROOT", str(DEFAULT_OUTPUT_ROOT)))


DATA_SET = [
    ["MERTENS", 6, 6],
    ["MERTENS", 2, 18],
    ["BOWMAN", 5, 20],
    ["JAESCHKE", 8, 6],
    ["JAESCHKE", 3, 18],
    ["JACKSON", 8, 7],
    ["JACKSON", 3, 21],
    ["MANSOOR", 4, 48],
    ["MANSOOR", 2, 94],
    ["MITCHELL", 8, 14],
    ["MITCHELL", 3, 39],
    ["ROSZIEG", 10, 14],
    ["ROSZIEG", 4, 32],
    ["BUXEY", 14, 25],
    ["BUXEY", 7, 47],
    ["SAWYER", 14, 25],
    ["SAWYER", 7, 47],
]

TEST_DATA_SET = [
    ["MERTENS", 6, 6, 3, 10],
    ["MANSOOR", 4, 48, 2, 6],
    ["MITCHELL", 8, 14, 3, 12],
    ["BUXEY", 14, 25, 1, 14],
    ["SAWYER", 14, 25, 2, 20],
]


@dataclass(frozen=True)
class Instance:
    name: str
    n: int
    m: int
    c: int
    r_max: int
    R_max: int
    durations: List[int]
    powers: List[int]
    precedence_edges: List[Tuple[int, int]]


@dataclass
class Coding:
    stations: List[List[int]]


@dataclass
class Solution:
    coding: Coding
    starts: List[int]
    assignments: List[int]
    res_counts: List[int]
    peak: int
    feasible: bool
    penalized_value: float
    decoder_status: str


@dataclass
class DecoderStats:
    exact_decoder_calls: int = 0
    heuristic_decoder_calls: int = 0
    infeasible_codings: int = 0
    time_spent_exact: float = 0.0
    time_spent_heuristic: float = 0.0

    @property
    def time_spent(self) -> float:
        return self.time_spent_exact + self.time_spent_heuristic


@dataclass
class MSLSResult:
    solution: Solution
    stats: DecoderStats
    starts_count: int
    runtime_sec: float


@dataclass
class DecoderContext:
    decoder_time_limit: float = 60.0
    extra_decoder_time_limit: float = 10.0
    deadline: Optional[float] = None
    log_cplex: bool = False
    stats: DecoderStats = field(default_factory=DecoderStats)
    exact_cache: Dict[Tuple[Tuple[Tuple[int, ...], ...], Tuple[int, ...]], Solution] = field(default_factory=dict)

    def remaining_time(self, fallback: float) -> float:
        if self.deadline is None:
            return fallback
        return max(0.0, min(fallback, self.deadline - time_module.time()))


SUMMARY_ROWS: List[Dict[str, Any]] = []


def read_input(instance_name: str) -> Tuple[int, List[int], List[Tuple[int, int]]]:
    input_path = DATA_DIR / f"{instance_name}.IN2"
    durations: List[int] = []
    edges: List[Tuple[int, int]] = []
    n = 0

    with input_path.open("r", encoding="utf-8") as f:
        for line_no, raw_line in enumerate(f):
            line = raw_line.strip()
            if not line:
                continue
            if line_no == 0:
                n = int(line)
            elif len(durations) < n:
                durations.append(int(line))
            else:
                left, right = line.split(",")
                if left == "-1" and right == "-1":
                    break
                edges.append((int(left) - 1, int(right) - 1))

    if n <= 0 or len(durations) != n:
        raise ValueError(f"Invalid precedence file for {instance_name}: n={n}, durations={len(durations)}")
    return n, durations, edges


def load_power(instance_name: str, n: int) -> List[int]:
    power_path = POWER_DIR / f"{instance_name}.txt"
    with power_path.open("r", encoding="utf-8") as f:
        powers = [int(line.strip()) for line in f if line.strip()]
    if len(powers) != n:
        raise ValueError(f"Power file length for {instance_name} is {len(powers)}, expected {n}")
    return powers


def build_instance(instance_name: str, m: int, c: int, r_max: int, R_max: int) -> Instance:
    n, durations, edges = read_input(instance_name)
    powers = load_power(instance_name, n)
    horizon = r_max * c
    too_long = [j + 1 for j, duration in enumerate(durations) if duration > horizon]
    if too_long:
        raise ValueError(f"Tasks exceed r_max*c={horizon}: {too_long}")
    return Instance(instance_name, n, m, c, r_max, R_max, durations, powers, edges)


def ubw(instance: Instance) -> int:
    count = min(instance.n, instance.R_max)
    return sum(sorted(instance.powers, reverse=True)[:count]) + 1


def normalize_coding(coding: Coding) -> Coding:
    return Coding([list(station) for station in coding.stations if station])


def coding_key(coding: Coding) -> Tuple[Tuple[int, ...], ...]:
    return tuple(tuple(station) for station in normalize_coding(coding).stations)


def flattened(coding: Coding) -> List[int]:
    return [task for station in coding.stations for task in station]


def validate_coding(instance: Instance, coding: Coding) -> bool:
    coding.stations = normalize_coding(coding).stations
    if len(coding.stations) > instance.m:
        raise ValueError(f"Coding has {len(coding.stations)} stations, exceeds m={instance.m}")
    flat = flattened(coding)
    if sorted(flat) != list(range(instance.n)):
        raise ValueError("Coding must contain every task exactly once")
    positions = {task: pos for pos, task in enumerate(flat)}
    for pred, succ in instance.precedence_edges:
        if positions[pred] >= positions[succ]:
            raise ValueError(f"Coding violates precedence {pred + 1}->{succ + 1}")
    return True


def assignments_from_coding(instance: Instance, coding: Coding) -> List[int]:
    assignments = [-1] * instance.n
    for k, station in enumerate(coding.stations):
        for task in station:
            assignments[task] = k
    return assignments


def station_workloads(instance: Instance, coding: Coding) -> List[int]:
    return [sum(instance.durations[j] for j in station) for station in coding.stations]


def resource_counts_for_coding(instance: Instance, coding: Coding) -> Tuple[List[int], List[int]]:
    workloads = station_workloads(instance, coding)
    res_counts = [max(1, math.ceil(workload / instance.c)) for workload in workloads]
    idle_times = [res * instance.c - workload for res, workload in zip(res_counts, workloads)]
    return res_counts, idle_times


def coding_penalty(instance: Instance, coding: Coding) -> int:
    res_counts, _ = resource_counts_for_coding(instance, coding)
    total_excess = max(0, sum(res_counts) - instance.R_max)
    station_excess = sum(max(0, res - instance.r_max) for res in res_counts)
    return total_excess + station_excess


def compute_peak(instance: Instance, starts: Sequence[int]) -> int:
    if len(starts) != instance.n:
        raise ValueError(f"starts length {len(starts)} != n={instance.n}")
    loads = [0] * instance.c
    for j, start in enumerate(starts):
        if start < 0:
            continue
        duration = instance.durations[j]
        power = instance.powers[j]
        for off in range(duration):
            loads[(start + off) % instance.c] += power
    return max(loads) if loads else 0


def add_task_to_profile(instance: Instance, profile: List[int], task: int, start: int) -> None:
    for off in range(instance.durations[task]):
        profile[(start + off) % instance.c] += instance.powers[task]


def validate_solution(instance: Instance, solution: Solution) -> bool:
    validate_coding(instance, solution.coding)
    if len(solution.starts) != instance.n:
        raise ValueError("Solution starts length mismatch")
    if len(solution.assignments) != instance.n:
        raise ValueError("Solution assignments length mismatch")

    coding_assignments = assignments_from_coding(instance, solution.coding)
    if coding_assignments != solution.assignments:
        raise ValueError("Solution assignments do not match coding")

    for station in solution.coding.stations:
        for left, right in zip(station, station[1:]):
            if solution.starts[left] + instance.durations[left] > solution.starts[right]:
                raise ValueError(f"Station order overlaps tasks {left + 1}, {right + 1}")

    verified_peak = compute_peak(instance, solution.starts)
    if verified_peak != solution.peak:
        raise ValueError(f"Peak mismatch: solution={solution.peak}, computed={verified_peak}")
    return True


def random_topological_order(instance: Instance, rng: random.Random) -> List[int]:
    successors = [[] for _ in range(instance.n)]
    indegree = [0] * instance.n
    for pred, succ in instance.precedence_edges:
        successors[pred].append(succ)
        indegree[succ] += 1

    available = [j for j in range(instance.n) if indegree[j] == 0]
    order: List[int] = []
    while available:
        idx = rng.randrange(len(available))
        task = available.pop(idx)
        order.append(task)
        for succ in successors[task]:
            indegree[succ] -= 1
            if indegree[succ] == 0:
                available.append(succ)

    if len(order) != instance.n:
        raise ValueError(f"Precedence graph for {instance.name} is cyclic")
    return order


def construction(instance: Instance, rng: random.Random) -> Coding:
    order = random_topological_order(instance, rng)
    station_count = rng.randint(1, min(instance.m, instance.n))
    if station_count == 1:
        coding = Coding([order])
    else:
        cuts = sorted(rng.sample(range(1, instance.n), station_count - 1))
        bounds = [0] + cuts + [instance.n]
        coding = Coding([order[bounds[i]:bounds[i + 1]] for i in range(station_count)])
    validate_coding(instance, coding)
    return coding


def make_solution(
    instance: Instance,
    coding: Coding,
    starts: List[int],
    res_counts: List[int],
    feasible: bool,
    decoder_status: str,
) -> Solution:
    assignments = assignments_from_coding(instance, coding)
    peak = compute_peak(instance, starts)
    penalty = coding_penalty(instance, coding)
    penalized_value = peak + penalty * ubw(instance)
    if feasible and penalty == 0:
        penalized_value = peak
    return Solution(coding, starts, assignments, list(res_counts), peak, feasible and penalty == 0, penalized_value, decoder_status)


def heur_decoder(instance: Instance, coding: Coding, ctx: Optional[DecoderContext] = None) -> Solution:
    t0 = time_module.time()
    if ctx:
        ctx.stats.heuristic_decoder_calls += 1

    coding = normalize_coding(coding)
    validate_coding(instance, coding)
    res_counts, idle_times = resource_counts_for_coding(instance, coding)
    starts = [-1] * instance.n
    profile = [0] * instance.c
    current_peak = 0
    status = "HEUR"

    station_order = sorted(range(len(coding.stations)), key=lambda k: (idle_times[k], k))
    for order_pos, k in enumerate(station_order):
        station = coding.stations[k]
        current_time = 0
        elapsed_in_station = 0

        for task in station:
            duration = instance.durations[task]
            if order_pos == 0:
                start = current_time
            else:
                d_e = elapsed_in_station
                d_l = d_e + idle_times[k]
                lo = max(current_time, d_e)
                hi = d_l
                if lo > hi:
                    start = lo
                    status = "HEUR_REPAIRED"
                else:
                    best_tuple: Optional[Tuple[int, int, int]] = None
                    best_start = lo
                    for candidate in range(lo, hi + 1):
                        new_profile = profile[:]
                        add_task_to_profile(instance, new_profile, task, candidate)
                        new_peak = max(new_profile)
                        increase = new_peak - current_peak
                        candidate_key = (increase, new_peak, candidate)
                        if best_tuple is None or candidate_key < best_tuple:
                            best_tuple = candidate_key
                            best_start = candidate
                    start = best_start

            starts[task] = start
            add_task_to_profile(instance, profile, task, start)
            current_peak = max(profile)
            current_time = start + duration
            elapsed_in_station += duration

    penalty = coding_penalty(instance, coding)
    solution = make_solution(instance, coding, starts, res_counts, penalty == 0, status)
    if penalty > 0:
        solution.feasible = False
        solution.penalized_value = solution.peak + penalty * ubw(instance)
    if ctx:
        ctx.stats.time_spent_heuristic += time_module.time() - t0
    return solution


def exact_decoder(
    instance: Instance,
    coding: Coding,
    res_counts: List[int],
    warmstart_solution: Optional[Solution] = None,
    time_limit: float = 60.0,
    ctx: Optional[DecoderContext] = None,
) -> Solution:
    coding = normalize_coding(coding)
    validate_coding(instance, coding)
    cache_key = (coding_key(coding), tuple(res_counts))
    if ctx and cache_key in ctx.exact_cache:
        return ctx.exact_cache[cache_key]

    if ctx:
        ctx.stats.exact_decoder_calls += 1
    t0 = time_module.time()

    if len(res_counts) != len(coding.stations):
        raise ValueError("res_counts length must match number of stations")

    time_limit = max(0.0, time_limit)
    fallback = warmstart_solution
    workloads = station_workloads(instance, coding)
    idle_times = [res * instance.c - workload for res, workload in zip(res_counts, workloads)]
    if any(idle < 0 for idle in idle_times) or time_limit <= 0:
        result = fallback if fallback is not None else exact_fail_solution(instance, coding, res_counts)
        if ctx:
            ctx.stats.time_spent_exact += time_module.time() - t0
            ctx.exact_cache[cache_key] = result
        return result

    mdl = Model(name=f"MPSC_sigma_{instance.name}")
    mdl.parameters.timelimit = time_limit
    mdl.parameters.threads = 1
    try:
        mdl.parameters.mip.display = 0
    except Exception:
        pass

    starts_by_pos: Dict[Tuple[int, int], List[int]] = {}
    start_vars: Dict[Tuple[int, int, int], Any] = {}
    for k, station in enumerate(coding.stations):
        d_e = 0
        for pos, task in enumerate(station):
            d_l = d_e + idle_times[k]
            valid_starts = list(range(d_e, d_l + 1))
            starts_by_pos[k, pos] = valid_starts
            for start in valid_starts:
                start_vars[k, pos, start] = mdl.binary_var(name=f"S_{k}_{pos}_{start}")
            d_e += instance.durations[task]

    W_M = mdl.integer_var(lb=0, name="W_M")

    for (k, pos), valid_starts in starts_by_pos.items():
        mdl.add_constraint(mdl.sum(start_vars[k, pos, start] for start in valid_starts) == 1)

    for k, station in enumerate(coding.stations):
        for pos in range(len(station) - 1):
            current_task = station[pos]
            current_duration = instance.durations[current_task]
            current_starts = starts_by_pos[k, pos]
            next_starts = starts_by_pos[k, pos + 1]
            for next_start in next_starts:
                rhs_terms = [
                    start_vars[k, pos, tau]
                    for tau in current_starts
                    if tau <= next_start - current_duration
                ]
                mdl.add_constraint(start_vars[k, pos + 1, next_start] <= mdl.sum(rhs_terms))

    for t_mod in range(instance.c):
        terms = []
        for k, station in enumerate(coding.stations):
            for pos, task in enumerate(station):
                duration = instance.durations[task]
                power = instance.powers[task]
                for start in starts_by_pos[k, pos]:
                    coeff = 0
                    for off in range(duration):
                        if (start + off) % instance.c == t_mod:
                            coeff += 1
                    if coeff:
                        terms.append(coeff * power * start_vars[k, pos, start])
        mdl.add_constraint(mdl.sum(terms) <= W_M)

    mdl.minimize(W_M)

    if warmstart_solution is not None:
        try:
            mip_start = mdl.new_solution()
            valid = True
            for k, station in enumerate(coding.stations):
                for pos, task in enumerate(station):
                    start = warmstart_solution.starts[task]
                    if (k, pos, start) not in start_vars:
                        valid = False
                        break
                    mip_start.add_var_value(start_vars[k, pos, start], 1)
                if not valid:
                    break
            if valid:
                mip_start.add_var_value(W_M, warmstart_solution.peak)
                mdl.add_mip_start(mip_start)
        except Exception:
            pass

    sol = mdl.solve(log_output=ctx.log_cplex if ctx else False)
    if sol:
        starts = [-1] * instance.n
        for k, station in enumerate(coding.stations):
            for pos, task in enumerate(station):
                selected = starts_by_pos[k, pos][0]
                for start in starts_by_pos[k, pos]:
                    if sol.get_value(start_vars[k, pos, start]) > 0.5:
                        selected = start
                        break
                starts[task] = selected
        result = make_solution(instance, coding, starts, res_counts, True, "EXACT")
    elif fallback is not None:
        result = make_solution(instance, coding, fallback.starts[:], res_counts, True, "EXACT_FALLBACK")
    else:
        result = exact_fail_solution(instance, coding, res_counts)

    if ctx:
        ctx.stats.time_spent_exact += time_module.time() - t0
        ctx.exact_cache[cache_key] = result
    return result


def exact_fail_solution(instance: Instance, coding: Coding, res_counts: List[int]) -> Solution:
    starts = [-1] * instance.n
    assignments = assignments_from_coding(instance, coding)
    return Solution(coding, starts, assignments, list(res_counts), ubw(instance), False, ubw(instance), "EXACT_FAIL")


def decoder(instance: Instance, coding: Coding, ctx: DecoderContext) -> Solution:
    sh = heur_decoder(instance, coding, ctx)
    penalty = coding_penalty(instance, coding)
    if penalty > 0:
        ctx.stats.infeasible_codings += 1
        sh.feasible = False
        sh.penalized_value = sh.peak + penalty * ubw(instance)
        sh.decoder_status = "PENALIZED_HEUR"
        return sh

    res_counts, _ = resource_counts_for_coding(instance, coding)
    s0 = exact_decoder(
        instance,
        coding,
        res_counts,
        warmstart_solution=sh,
        time_limit=ctx.remaining_time(ctx.decoder_time_limit),
        ctx=ctx,
    )
    best = s0
    current_res_counts = list(res_counts)

    while sum(current_res_counts) < instance.R_max and ctx.remaining_time(1.0) > 0:
        candidates = [k for k, res in enumerate(current_res_counts) if res < instance.r_max]
        if not candidates:
            break

        best_trial: Optional[Tuple[int, int, Solution, List[int]]] = None
        for k in candidates:
            trial_res_counts = current_res_counts[:]
            trial_res_counts[k] += 1
            trial = exact_decoder(
                instance,
                coding,
                trial_res_counts,
                warmstart_solution=best,
                time_limit=ctx.remaining_time(ctx.extra_decoder_time_limit),
                ctx=ctx,
            )
            trial_key = (trial.peak, k, trial, trial_res_counts)
            if best_trial is None or trial_key[0:2] < best_trial[0:2]:
                best_trial = trial_key

        if best_trial is None:
            break
        trial_peak, _, trial_solution, trial_res_counts = best_trial
        if trial_peak < best.peak:
            current_res_counts = trial_res_counts
            best = trial_solution
        else:
            break

    best.feasible = True
    best.penalized_value = best.peak
    return best


def insertion_neighbors(instance: Instance, coding: Coding, rng: random.Random) -> List[Coding]:
    coding = normalize_coding(coding)
    if not coding.stations:
        return []

    source_k = rng.randrange(len(coding.stations))
    source_station = coding.stations[source_k]
    task = source_station[rng.randrange(len(source_station))]
    original_key = coding_key(coding)

    base_stations = []
    removed = False
    for station in coding.stations:
        new_station = []
        for item in station:
            if item == task and not removed:
                removed = True
                continue
            new_station.append(item)
        if new_station:
            base_stations.append(new_station)

    seen = set()
    neighbors: List[Coding] = []

    def add_candidate(stations: List[List[int]]) -> None:
        candidate = normalize_coding(Coding([list(station) for station in stations]))
        key = coding_key(candidate)
        if key == original_key or key in seen:
            return
        seen.add(key)
        try:
            validate_coding(instance, candidate)
        except ValueError:
            return
        neighbors.append(candidate)

    for target_k in range(len(base_stations)):
        for pos in range(len(base_stations[target_k]) + 1):
            stations = [list(station) for station in base_stations]
            stations[target_k].insert(pos, task)
            add_candidate(stations)

    if len(base_stations) < instance.m:
        for station_pos in range(len(base_stations) + 1):
            stations = [list(station) for station in base_stations]
            stations.insert(station_pos, [task])
            add_candidate(stations)

    return neighbors


def get_neighbors_n2(instance: Instance, coding: Coding, rng: random.Random, ctx: DecoderContext) -> Optional[Solution]:
    candidates = insertion_neighbors(instance, coding, rng)
    best: Optional[Solution] = None
    for candidate in candidates:
        if ctx.remaining_time(0.0) <= 0:
            break
        sol = decoder(instance, candidate, ctx)
        if best is None or solution_order(sol) < solution_order(best):
            best = sol
    return best


def solution_order(solution: Solution) -> Tuple[float, int, int]:
    return (solution.penalized_value, 0 if solution.feasible else 1, solution.peak)


def msxlspsc(
    instance: Instance,
    global_time_limit: float = 600.0,
    seed: Optional[int] = None,
    decoder_time_limit: float = 60.0,
    extra_decoder_time_limit: float = 10.0,
) -> MSLSResult:
    rng = random.Random(seed)
    start_time = time_module.time()
    ctx = DecoderContext(
        decoder_time_limit=decoder_time_limit,
        extra_decoder_time_limit=extra_decoder_time_limit,
        deadline=start_time + global_time_limit,
    )

    best_feasible: Optional[Solution] = None
    best_any: Optional[Solution] = None
    starts_count = 0

    while time_module.time() < ctx.deadline:
        starts_count += 1
        coding = construction(instance, rng)
        current = decoder(instance, coding, ctx)
        best_any = current if best_any is None or solution_order(current) < solution_order(best_any) else best_any
        if current.feasible and (best_feasible is None or current.peak < best_feasible.peak):
            best_feasible = current

        no_improve = 0
        while no_improve < 50 and time_module.time() < ctx.deadline:
            neighbor = get_neighbors_n2(instance, current.coding, rng, ctx)
            if neighbor is None:
                no_improve += 1
                continue

            if neighbor.penalized_value <= current.penalized_value:
                if neighbor.penalized_value < current.penalized_value:
                    no_improve = 0
                else:
                    no_improve += 1
                current = neighbor
            else:
                no_improve += 1

            best_any = current if best_any is None or solution_order(current) < solution_order(best_any) else best_any
            if current.feasible and (best_feasible is None or current.peak < best_feasible.peak):
                best_feasible = current

    runtime = time_module.time() - start_time
    if best_feasible is None:
        if best_any is None:
            coding = construction(instance, rng)
            best_any = heur_decoder(instance, coding, ctx)
        result_solution = best_any
    else:
        result_solution = best_feasible

    return MSLSResult(result_solution, ctx.stats, starts_count, runtime)


def html_schedule_path(instance: Instance) -> Tuple[Path, Path]:
    out_dir = OUTPUT_ROOT / f"{instance.name}_n{instance.n}_m{instance.m}_c{instance.c}" / f"r{instance.r_max}_R{instance.R_max}"
    outfile = out_dir / f"{instance.name}_n{instance.n}_m{instance.m}_c{instance.c}_r{instance.r_max}_R{instance.R_max}.html"
    return out_dir, outfile


def write_html_schedule(instance: Instance, solution: Solution, runtime_sec: float) -> Path:
    out_dir, outfile = html_schedule_path(instance)
    out_dir.mkdir(parents=True, exist_ok=True)
    if outfile.exists():
        outfile.unlink()

    compact = []
    for k in range(instance.m):
        machine_rows = [[0 for _ in range(instance.c)] for _ in range(instance.r_max)]
        for j in range(instance.n):
            if solution.assignments[j] != k:
                continue
            start = solution.starts[j]
            if start < 0:
                continue
            for off in range(instance.durations[j]):
                t_abs = start + off
                row = t_abs // instance.c
                col = t_abs % instance.c
                if 0 <= row < instance.r_max:
                    machine_rows[row][col] = j + 1
        compact.append(machine_rows)

    header_cells = "".join(f"<th>t{t}</th>" for t in range(instance.c))
    rows_html = []
    for k in range(instance.m):
        res = solution.res_counts[k] if k < len(solution.res_counts) else 0
        rows_html.append(f"<tr class='machine'><th colspan='{instance.c + 1}'>Machine {k + 1} (r={res})</th></tr>")
        rows_html.append(f"<tr><th></th>{header_cells}</tr>")
        for r in range(instance.r_max):
            cells = "".join(f"<td>{compact[k][r][t] if compact[k][r][t] else ''}</td>" for t in range(instance.c))
            rows_html.append(f"<tr><th>Res {r + 1}</th>{cells}</tr>")

    starts_text = "<br>".join(
        f"Task {j + 1}: machine {solution.assignments[j] + 1} start {solution.starts[j]}"
        for j in range(instance.n)
    )
    resources_text = "<br>".join(
        f"Machine {k + 1}: {solution.res_counts[k] if k < len(solution.res_counts) else 0} resources"
        for k in range(instance.m)
    )

    html = f"""<!DOCTYPE html>
<html>
<head>
<meta charset="utf-8">
<style>
table {{ border-collapse: collapse; font-family: Arial, sans-serif; }}
th, td {{ border: 1px solid #aaa; padding: 4px 6px; text-align: center; }}
th {{ background: #f0f0f0; position: sticky; top: 0; }}
.meta {{ margin-bottom: 10px; font-family: Arial, sans-serif; }}
.machine th {{ background: #dfe8ff; }}
</style>
</head>
<body>
<div class="meta">
<strong>Instance:</strong> {instance.name} &nbsp;
<strong>m:</strong> {instance.m} &nbsp;
<strong>c:</strong> {instance.c} &nbsp;
<strong>r_max:</strong> {instance.r_max} &nbsp;
<strong>R_max:</strong> {instance.R_max} &nbsp;
<strong>Peak:</strong> {solution.peak} &nbsp;
<strong>Runtime:</strong> {runtime_sec:.3f}s<br>
<strong>Resources per machine:</strong><br>
{resources_text}<br>
<strong>Starts:</strong><br>
{starts_text}
</div>
<table>
<tr><th>Machine/Time</th>{header_cells}</tr>
{''.join(rows_html)}
</table>
</body>
</html>
"""
    outfile.write_text(html, encoding="utf-8")
    return outfile


def flush_summary(final: bool = False) -> None:
    if not SUMMARY_ROWS:
        return
    OUTPUT_ROOT.mkdir(parents=True, exist_ok=True)
    csv_path = OUTPUT_ROOT / "summary.csv"
    existing: List[Dict[str, Any]] = []
    if csv_path.exists():
        with csv_path.open("r", encoding="utf-8") as f:
            existing.extend(csv.DictReader(f))

    def key(row: Dict[str, Any]) -> Tuple[str, ...]:
        return (
            str(row.get("name", "")),
            str(row.get("n", "")),
            str(row.get("m", "")),
            str(row.get("c", "")),
            str(row.get("r_max", "")),
            str(row.get("R_max", "")),
            str(row.get("seed", "")),
            str(row.get("replication", "")),
        )

    merged = {key(row): row for row in existing}
    for row in SUMMARY_ROWS:
        merged[key(row)] = row

    fieldnames = [
        "name",
        "n",
        "m",
        "c",
        "r_max",
        "R_max",
        "seed",
        "replication",
        "starts_count",
        "exact_decoder_calls",
        "heuristic_decoder_calls",
        "infeasible_codings",
        "best_peak",
        "feasible",
        "penalized_value",
        "runtime_sec",
        "decoder_status",
    ]
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames, extrasaction="ignore")
        writer.writeheader()
        writer.writerows(merged.values())

    if final:
        try:
            import pandas as pd  # type: ignore

            pd.DataFrame(list(merged.values())).to_excel(OUTPUT_ROOT / "summary.xlsx", index=False)
        except Exception:
            pass
    SUMMARY_ROWS.clear()


def add_summary_row(
    instance: Instance,
    seed: Optional[int],
    replication: int,
    starts_count: int,
    stats: DecoderStats,
    solution: Solution,
    runtime_sec: float,
) -> None:
    SUMMARY_ROWS.append(
        {
            "name": instance.name,
            "n": instance.n,
            "m": instance.m,
            "c": instance.c,
            "r_max": instance.r_max,
            "R_max": instance.R_max,
            "seed": "" if seed is None else seed,
            "replication": replication,
            "starts_count": starts_count,
            "exact_decoder_calls": stats.exact_decoder_calls,
            "heuristic_decoder_calls": stats.heuristic_decoder_calls,
            "infeasible_codings": stats.infeasible_codings,
            "best_peak": solution.peak if solution.feasible else "",
            "feasible": solution.feasible,
            "penalized_value": round(solution.penalized_value, 3),
            "runtime_sec": round(runtime_sec, 3),
            "decoder_status": solution.decoder_status,
        }
    )
    flush_summary(final=True)


def resolve_runs(args: argparse.Namespace) -> List[Tuple[int, str, int, int, int, int]]:
    if args.instance_id is not None:
        dataset = TEST_DATA_SET if args.test else DATA_SET
        base = dataset[args.instance_id]
        if args.r_max is None or args.R_max is None:
            if args.test and len(base) >= 5:
                return [(args.instance_id, base[0], base[1], base[2], base[3], base[4])]
            raise SystemExit("Single-instance mode requires: <instance_id> <r_max> <R_max>")
        return [(args.instance_id, base[0], base[1], base[2], args.r_max, args.R_max)]

    runs = []
    if args.test:
        for instance_id, row in enumerate(TEST_DATA_SET):
            runs.append((instance_id, row[0], row[1], row[2], row[3], row[4]))
    else:
        for instance_id, row in enumerate(DATA_SET):
            for r_max in range(1, 4):
                for R_max in range(row[1], r_max * row[1] + 1):
                    runs.append((instance_id, row[0], row[1], row[2], r_max, R_max))
    return runs


def run_one(instance: Instance, args: argparse.Namespace, seed: Optional[int], replication: int) -> Solution:
    result = msxlspsc(
        instance,
        global_time_limit=args.ms_time_limit,
        seed=seed,
        decoder_time_limit=args.decoder_time_limit,
        extra_decoder_time_limit=args.extra_decoder_time_limit,
    )
    add_summary_row(instance, seed, replication, result.starts_count, result.stats, result.solution, result.runtime_sec)
    if args.html or args.write_html:
        outfile = write_html_schedule(instance, result.solution, result.runtime_sec)
        print(f"HTML schedule written to {outfile}")
    print(
        f"MSLS {instance.name}: peak={result.solution.peak} feasible={result.solution.feasible} "
        f"penalized={result.solution.penalized_value} starts={result.starts_count} "
        f"exact_calls={result.stats.exact_decoder_calls} runtime={result.runtime_sec:.3f}s"
    )
    return result.solution


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="MSxLSPSC/MS04 matheuristic.")
    parser.add_argument("instance_id", nargs="?", type=int)
    parser.add_argument("r_max", nargs="?", type=int)
    parser.add_argument("R_max", nargs="?", type=int)
    parser.add_argument("--ms-time-limit", type=float, default=600.0)
    parser.add_argument("--decoder-time-limit", type=float, default=60.0)
    parser.add_argument("--extra-decoder-time-limit", type=float, default=10.0)
    parser.add_argument("--seed", type=int, default=0)
    parser.add_argument("--replications", type=int, default=1)
    parser.add_argument("--test", action="store_true")
    parser.add_argument("--html", action="store_true")
    parser.add_argument("--write-html", action="store_true")
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    runs = resolve_runs(args)
    for _, inst_name, m, c, r_max, R_max in runs:
        instance = build_instance(inst_name, m, c, r_max, R_max)
        for replication in range(args.replications):
            seed = None if args.seed is None else args.seed + replication
            run_one(instance, args, seed, replication)


if __name__ == "__main__":
    main()
