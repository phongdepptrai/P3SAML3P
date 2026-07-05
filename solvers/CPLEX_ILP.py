"""
CPLEX ILP Solver for P3SAML3P Assembly Line Balancing.

Implements the ILP formulation (Eq 2–12) using docplex.
Since the CPLEX Python package has been successfully linked to the full system CPLEX Academic Edition,
we can solve models of any size natively without size limits.
"""

import math
import time as time_module
import os
import sys
import csv
from pathlib import Path
from typing import List, Dict, Any

from docplex.mp.model import Model
from docplex.mp.progress import ProgressListener, ProgressClock

# ─── Global variables ───────────────────────────────────────────────────────
time_list = []
adj = []
neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
reversed_neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
W = []
name = ""
m = 0
c = 0
r_max = 0
R_max = 0
n = 0
summary_rows: List[Dict[str, Any]] = []

SCRIPT_NAME = Path(__file__).name
SCRIPT_PATH = Path(__file__).resolve().as_posix()
PROJECT_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_OUTPUT_ROOT = PROJECT_ROOT / "Output" / Path(__file__).stem
OUTPUT_ROOT = Path(os.environ.get("OUTPUT_ROOT", str(DEFAULT_OUTPUT_ROOT)))
DATA_DIR = PROJECT_ROOT / "presedent_graph"
POWER_DIR = PROJECT_ROOT / "official_task_power"
WRITE_HTML = False  # Set to True via --write-html flag
TIMEOUT = 600  # CPLEX time limit in seconds


# ─── Summary CSV I/O ────────────────────────────────────────────────────────

def flush_summary(final=False):
    """Write summary rows replacing any existing entry with the same key."""
    if not summary_rows:
        return

    def key(row: Dict[str, Any]):
        return (
            str(row["name"]),
            str(row["n"]),
            str(row["m"]),
            str(row["c"]),
            str(row["r_max"]),
            str(row["R_max"]),
        )

    out_dir = OUTPUT_ROOT
    out_dir.mkdir(parents=True, exist_ok=True)
    csv_path = out_dir / "summary.csv"

    existing: List[Dict[str, Any]] = []
    if csv_path.exists():
        with csv_path.open("r", encoding="utf-8") as f:
            reader = csv.DictReader(f)
            for row in reader:
                existing.append(row)

    # Replace entries with the same key (keep latest)
    merged_map: Dict[tuple, Dict[str, Any]] = {}
    for row in existing:
        merged_map[key(row)] = row
    for row in summary_rows:
        merged_map[key(row)] = row

    merged = list(merged_map.values())
    if not merged:
        return

    fieldnames = list(merged[0].keys())
    with csv_path.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(merged)

    # XLSX if pandas available — only write on final execution to avoid overhead
    if final:
        try:
            import pandas as pd  # type: ignore
            df = pd.DataFrame(merged)
            xlsx_path = out_dir / "summary.xlsx"
            df.to_excel(xlsx_path, index=False)
        except Exception:
            pass

    summary_rows.clear()


def add_summary_row(status: str, peak: Any, attempts: int, runtime_sec: float,
                    ilp_vars: int, ilp_constraints: int):
    """Append a summary row and flush it to disk."""
    summary_rows.append(
        {
            "name": name,
            "n": n,
            "m": m,
            "c": c,
            "r_max": r_max,
            "R_max": R_max,
            "ilp_vars": ilp_vars,
            "ilp_constraints": ilp_constraints,
            "peak": peak,
            "attempts": attempts,
            "runtime_sec": round(runtime_sec, 3),
            "status": status,
        }
    )
    is_final = status in ("OPTIMAL", "TIMEOUT_INFEASIBLE", "FEASIBLE_TIMEOUT")
    flush_summary(final=is_final)


# ─── Data sets ───────────────────────────────────────────────────────────────

data_set = [
    # Easy families
    # MERTENS
    ["MERTENS", 6, 6],      # 0
    ["MERTENS", 2, 18],     # 1

    # BOWMAN
    ["BOWMAN", 5, 20],      # 2

    # JAESCHKE
    ["JAESCHKE", 8, 6],     # 3
    ["JAESCHKE", 3, 18],    # 4

    # JACKSON
    ["JACKSON", 8, 7],      # 5
    ["JACKSON", 3, 21],     # 6

    # MANSOOR
    ["MANSOOR", 4, 48],     # 7
    ["MANSOOR", 2, 94],     # 8

    # MITCHELL
    ["MITCHELL", 8, 14],    # 9
    ["MITCHELL", 3, 39],    # 10

    # ROSZIEG
    ["ROSZIEG", 10, 14],    # 11
    ["ROSZIEG", 4, 32],     # 12

    # Hard families
    # BUXEY
    ["BUXEY", 14, 25],      # 13
    ["BUXEY", 7, 47],       # 14

    # SAWYER
    ["SAWYER", 14, 25],     # 15
    ["SAWYER", 7, 47],      # 16
]

test_data_set = [
    ["MERTENS", 6, 6, 3, 10],
    ["MANSOOR", 4, 48, 2, 6],
    ["MITCHELL", 8, 14, 3, 12],
    ["BUXEY", 14, 25, 1, 14],
    ["SAWYER", 14, 25, 2, 20],
]


# ─── Globals reset ──────────────────────────────────────────────────────────

def refresh_globals():
    global time_list, adj, neighbors, reversed_neighbors, W, n
    time_list = []
    adj = []
    neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    reversed_neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    W = []


# ─── Input reading ──────────────────────────────────────────────────────────

def read_input(instance_name):
    """Parse the .IN2 precedence graph file."""
    cnt = 0
    global n, time_list, adj, neighbors, reversed_neighbors
    input_path = DATA_DIR / f"{instance_name}.IN2"
    with input_path.open("r", encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if line:
                if cnt == 0:
                    n = int(line)
                elif cnt <= n:
                    time_list.append(int(line))
                else:
                    parts = line.split(",")
                    if parts[0] != "-1" and parts[1] != "-1":
                        i_task = int(parts[0]) - 1
                        j_task = int(parts[1]) - 1
                        adj.append([i_task, j_task])
                        neighbors[i_task][j_task] = 1
                        reversed_neighbors[j_task][i_task] = 1
                    else:
                        break
                cnt += 1


def load_power(instance_name):
    """Read task power values for the given instance name."""
    global W
    power_path = POWER_DIR / f"{instance_name}.txt"
    with power_path.open("r", encoding="utf-8") as f:
        W = [int(line.strip()) for line in f if line.strip()]


# ─── HTML output (compact table) ────────────────────────────────────────────

def html_schedule_path(instance_name, n_val, m_val, c_val, r_max_val, R_max_val):
    out_dir = OUTPUT_ROOT / f"{instance_name}_n{n_val}_m{m_val}_c{c_val}" / f"r{r_max_val}_R{R_max_val}"
    outfile = out_dir / f"{instance_name}_n{n_val}_m{m_val}_c{c_val}_r{r_max_val}_R{R_max_val}.html"
    return out_dir, outfile


def write_html_schedule(instance_name, m_val, c_val, r_max_val, R_max_val,
                        assignments, starts, res_counts, peak, runtime_sec):
    """Write an HTML table for the ILP solution schedule."""
    out_dir, outfile = html_schedule_path(instance_name, n, m_val, c_val, r_max_val, R_max_val)
    out_dir.mkdir(parents=True, exist_ok=True)
    if outfile.exists():
        outfile.unlink()

    horizon = c_val * r_max_val
    # Build compact table: for each machine, r_max rows x c cols
    compact = []
    for k in range(m_val):
        machine_rows = [[0 for _ in range(c_val)] for _ in range(r_max_val)]
        for j in range(n):
            if assignments[j] != k:
                continue
            st = starts[j]
            for off in range(time_list[j]):
                t_abs = st + off
                row = t_abs // c_val
                col = t_abs % c_val
                if 0 <= row < r_max_val:
                    machine_rows[row][col] = j + 1
        compact.append(machine_rows)

    header_cells = "".join([f"<th>t{t}</th>" for t in range(c_val)])
    rows_html = []
    for k in range(m_val):
        rows_html.append(f"<tr class='machine'><th colspan='{c_val+1}'>Machine {k+1} (r={res_counts[k]})</th></tr>")
        rows_html.append(f"<tr><th></th>{header_cells}</tr>")
        for r in range(r_max_val):
            cells = "".join([f"<td>{compact[k][r][t] if compact[k][r][t] else ''}</td>" for t in range(c_val)])
            rows_html.append(f"<tr><th>Res {r+1}</th>{cells}</tr>")

    starts_text = "<br>".join(
        [f"Task {j+1}: machine {assignments[j]+1} start {starts[j]}" for j in range(n)]
    )
    resources_text = "<br>".join([f"Machine {k+1}: {res_counts[k]} resources" for k in range(m_val)])

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
<strong>Instance:</strong> {instance_name} &nbsp;
<strong>m:</strong> {m_val} &nbsp;
<strong>c:</strong> {c_val} &nbsp;
<strong>r_max:</strong> {r_max_val} &nbsp;
<strong>R_max:</strong> {R_max_val} &nbsp;
<strong>Peak:</strong> {peak if peak is not None else 'NA'} &nbsp;
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


# ─── Docplex Progress Listener ──────────────────────────────────────────────

class IntermediatePeakLogger(ProgressListener):
    def __init__(self, ilp_vars, ilp_constraints, t_start):
        super().__init__(ProgressClock.Objective)
        self.ilp_vars = ilp_vars
        self.ilp_constraints = ilp_constraints
        self.t_start = t_start
        self.last_peak = None
        self.attempts = 0

    def notify_progress(self, pdata):
        if pdata.has_incumbent and pdata.current_objective is not None:
            peak_val = int(round(pdata.current_objective))
            if peak_val != self.last_peak:
                self.last_peak = peak_val
                self.attempts += 1
                elapsed = time_module.time() - self.t_start
                add_summary_row(
                    status="INTERMEDIATE",
                    peak=peak_val,
                    attempts=self.attempts,
                    runtime_sec=elapsed,
                    ilp_vars=self.ilp_vars,
                    ilp_constraints=self.ilp_constraints
                )


# ─── ILP model building and solving ─────────────────────────────────────────

def run_single_instance(name_param, m_param, c_param, r_max_param, R_max_param):
    """Build and solve the ILP model for a single problem instance."""
    global name, m, c, r_max, R_max
    name = name_param
    m = m_param
    c = c_param
    r_max = r_max_param
    R_max = R_max_param

    refresh_globals()
    read_input(name)
    load_power(name)

    horizon = c * r_max
    print(f"CPLEX ILP Solver (Native Docplex Mode)")
    print(f"Solving {name} with n={n}, m={m}, c={c}, r_max={r_max}, R_max={R_max}")
    print(f"horizon={horizon}, |adj|={len(adj)}")

    t_start = time_module.time()

    # ── Build the ILP model ──────────────────────────────────────────────
    mdl = Model(name=f'P3SAML3P_{name}_m{m}_c{c}_r{r_max}_R{R_max}')
    mdl.parameters.timelimit = TIMEOUT
    mdl.parameters.threads = 1

    # ── Decision variables ───────────────────────────────────────────────

    # X[j,k] ∈ {0,1}: task j assigned to workstation k
    X = {(j, k): mdl.binary_var(name=f'X_{j}_{k}')
         for j in range(n) for k in range(m)}

    # S[j,t] ∈ {0,1}: task j starts at time t
    valid_starts = {}
    S = {}
    for j in range(n):
        tj = time_list[j]
        latest = horizon - tj
        valid_starts[j] = list(range(latest + 1))
        for t in valid_starts[j]:
            S[j, t] = mdl.binary_var(name=f'S_{j}_{t}')

    # R[k,r] ∈ {0,1}: r-th resource activated at workstation k (0-indexed)
    R_var = {(k, r): mdl.binary_var(name=f'R_{k}_{r}')
             for k in range(m) for r in range(r_max)}

    # W_M ∈ Z+: peak power
    W_M = mdl.integer_var(lb=0, name='W_M')

    # Helper: F(j, t_abs)
    F_cache = {}

    def F(j, t_abs):
        if (j, t_abs) in F_cache:
            return F_cache[(j, t_abs)]
        tj = time_list[j]
        tau_lo = max(0, t_abs - tj + 1)
        tau_hi = min(t_abs, horizon - tj)
        terms = [S[j, tau] for tau in range(tau_lo, tau_hi + 1) if (j, tau) in S]
        expr = mdl.sum(terms)
        F_cache[(j, t_abs)] = expr
        return expr

    # ── Objective (Eq 2): Minimize W_M ───────────────────────────────────
    mdl.minimize(W_M)

    # ── Eq 3: Assignment — each task to exactly one workstation ──────────
    for j in range(n):
        mdl.add_constraint(
            mdl.sum(X[j, k] for k in range(m)) == 1
        )

    # ── Eq 4: Workload capacity per station ──────────────────────────────
    for k in range(m):
        mdl.add_constraint(
            mdl.sum(time_list[j] * X[j, k] for j in range(n)) <=
            c * mdl.sum(R_var[k, r] for r in range(r_max))
        )

    # ── Eq 5: Precedence arcs only — station ordering ────────────────────
    for i_task, j_task in adj:
        for k in range(m):
            mdl.add_constraint(
                X[j_task, k] <= mdl.sum(X[i_task, h] for h in range(k + 1))
            )

    # ── Eq 6: Unique start time ──────────────────────────────────────────
    for j in range(n):
        mdl.add_constraint(
            mdl.sum(S[j, t] for t in valid_starts[j]) == 1
        )

    # ── Eq 7: Resource bound — task start vs active resources ────────────
    for j in range(n):
        tj = time_list[j]
        for k in range(m):
            for r_idx in range(r_max):
                # Python r_idx is 0-based: inactive R[k,r_idx] means j must finish by r_idx*c.
                upper_t = r_idx * c - tj
                if upper_t >= 0:
                    mdl.add_constraint(
                        X[j, k] - R_var[k, r_idx] <=
                        mdl.sum(S[j, t] for t in range(upper_t + 1)
                                if (j, t) in S)
                    )
                else:
                    mdl.add_constraint(X[j, k] <= R_var[k, r_idx])

    # ── Eq 8: Precedence arcs only — time ordering on same station ───────
    for i_task, j_task in adj:
        ti = time_list[i_task]
        for k in range(m):
            for t in valid_starts[j_task]:
                upper_tau = t - ti
                rhs_terms = [S[i_task, tau]
                             for tau in range(max(0, upper_tau + 1))
                             if (i_task, tau) in S]
                mdl.add_constraint(
                    S[j_task, t] <=
                    mdl.sum(rhs_terms) + 2 - X[i_task, k] - X[j_task, k]
                )

    # ── Eq 9: Non-overlapping ────────────────────────────────────────────
    for i_task in range(n - 1):
        for j_task in range(i_task + 1, n):
            for k in range(m):
                for t_abs in range(horizon):
                    f_i = F(i_task, t_abs)
                    f_j = F(j_task, t_abs)
                    mdl.add_constraint(
                        X[i_task, k] + X[j_task, k] + f_i + f_j <= 3
                    )

    # ── Eq 10: Power peak ────────────────────────────────────────────────
    for t_mod in range(c):
        power_terms = []
        for j in range(n):
            wj = W[j] if j < len(W) else 0
            if wj == 0:
                continue
            for r_idx in range(r_max):
                t_abs = r_idx * c + t_mod
                f_jt = F(j, t_abs)
                power_terms.append(wj * f_jt)
        if power_terms:
            mdl.add_constraint(mdl.sum(power_terms) <= W_M)

    # ── Eq 11: Resource symmetry breaking ────────────────────────────────
    for k in range(m):
        for r_idx in range(r_max - 1):
            mdl.add_constraint(R_var[k, r_idx + 1] <= R_var[k, r_idx])

    # ── Eq 12: Total resource budget ─────────────────────────────────────
    mdl.add_constraint(
        mdl.sum(R_var[k, r] for k in range(m) for r in range(r_max)) <= R_max
    )

    # ── Solve ────────────────────────────────────────────────────────────
    num_vars = mdl.number_of_variables
    num_constrs = mdl.number_of_constraints
    build_time = time_module.time() - t_start
    print(f"Model built natively: {num_vars} variables, {num_constrs} constraints "
          f"(build time: {build_time:.3f}s)")

    add_summary_row(
        status="STARTED", peak="", attempts=0,
        runtime_sec=0.0, ilp_vars=num_vars, ilp_constraints=num_constrs,
    )

    # Register the real-time progress logger callback
    progress_logger = IntermediatePeakLogger(num_vars, num_constrs, t_start)
    mdl.add_progress_listener(progress_logger)

    sol = mdl.solve(log_output=True)
    runtime = time_module.time() - t_start
    attempts = progress_logger.attempts

    # ── Extract and report solution ──────────────────────────────────────
    if sol:
        peak = int(round(sol.get_value(W_M)))
        gap = mdl.solve_details.mip_relative_gap
        if attempts == 0:
            attempts = 1

        # Extract assignments and start times
        assignments = []
        starts_list = []
        for j in range(n):
            station = next(k for k in range(m) if sol.get_value(X[j, k]) > 0.5)
            start = next(t for t in valid_starts[j] if sol.get_value(S[j, t]) > 0.5)
            assignments.append(station)
            starts_list.append(start)

        # Extract resource counts per station
        res_counts = []
        for k in range(m):
            used = 0
            for r_idx in range(r_max):
                if sol.get_value(R_var[k, r_idx]) > 0.5:
                    used = r_idx + 1
            res_counts.append(used)

        # Print solution summary
        print(f"\n{'='*60}")
        if gap is not None and gap < 1e-6:
            status_str = "OPTIMAL"
            print(f"OPTIMAL peak: {peak} | attempts: {attempts} | runtime: {runtime:.3f}s")
        else:
            status_str = "FEASIBLE_TIMEOUT"
            print(f"Best peak found: {peak} | gap: {gap:.4%} | attempts: {attempts} | runtime: {runtime:.3f}s")

        for j in range(n):
            print(f"  task {j+1}: machine {assignments[j]+1} start {starts_list[j]}")

        print(f"  Resources: {res_counts}")
        total_res = sum(res_counts)
        print(f"  Total resources used: {total_res} / {R_max}")

        # Verify peak by computing it from start times
        verified_peak = 0
        for t_mod in range(c):
            load_at_t = 0
            for j in range(n):
                wj = W[j] if j < len(W) else 0
                st = starts_list[j]
                if st >= 0:
                    dur = time_list[j]
                    for r_idx in range(r_max):
                        t_abs = r_idx * c + t_mod
                        if st <= t_abs < st + dur:
                            load_at_t += wj
            verified_peak = max(verified_peak, load_at_t)
        print(f"  Verified peak: {verified_peak}")
        if verified_peak != peak:
            print(f"  ⚠ WARNING: verified peak ({verified_peak}) != W_M ({peak})")

        if WRITE_HTML:
            outfile = write_html_schedule(
                name, m, c, r_max, R_max,
                assignments, starts_list, res_counts, peak, runtime
            )
            if outfile:
                print(f"  HTML schedule written to {outfile}")

        add_summary_row(
            status=status_str, peak=peak, attempts=attempts,
            runtime_sec=runtime, ilp_vars=num_vars, ilp_constraints=num_constrs,
        )
    else:
        print(f"\nNo solution found | runtime: {runtime:.3f}s")
        add_summary_row(
            status="TIMEOUT_INFEASIBLE", peak="", attempts=attempts,
            runtime_sec=runtime, ilp_vars=num_vars, ilp_constraints=num_constrs,
        )


# ─── Main entry point ───────────────────────────────────────────────────────

if __name__ == "__main__":
    # Parse --write-html or --html flag
    if "--write-html" in sys.argv or "--html" in sys.argv:
        WRITE_HTML = True
        sys.argv = [a for a in sys.argv if a not in ("--write-html", "--html")]
        print("HTML schedule output enabled")

    is_test = False
    if "--test" in sys.argv:
        is_test = True
        sys.argv = [a for a in sys.argv if a != "--test"]

    if len(sys.argv) == 1:
        # Batch mode: run all instances with DOcplex directly.
        print("Run all instances (batch mode, native DOcplex)")
        completed_runs = set()
        summary_csv = OUTPUT_ROOT / "summary.csv"
        if summary_csv.exists():
            with summary_csv.open("r", encoding="utf-8") as f:
                for row in csv.DictReader(f):
                    completed_runs.add(
                        (
                            str(row.get("name", "")),
                            str(row.get("m", "")),
                            str(row.get("c", "")),
                            str(row.get("r_max", "")),
                            str(row.get("R_max", "")),
                        )
                    )

        runs = []
        if is_test:
            for instance_id, instance in enumerate(test_data_set):
                runs.append((instance_id, instance[0], instance[1], instance[2],
                             instance[3], instance[4]))
        else:
            for instance_id, instance in enumerate(data_set):
                inst_name = instance[0]
                inst_m = instance[1]
                inst_c = instance[2]
                for inst_r_max in range(1, 4):
                    for inst_R_max in range(inst_m, inst_r_max * inst_m + 1):
                        runs.append((instance_id, inst_name, inst_m, inst_c,
                                     inst_r_max, inst_R_max))

        for instance_id, inst_name, inst_m, inst_c, inst_r_max, inst_R_max in runs:
            try:
                key = (str(inst_name), str(inst_m), str(inst_c),
                       str(inst_r_max), str(inst_R_max))
                if key in completed_runs:
                    if WRITE_HTML:
                        refresh_globals()
                        read_input(inst_name)
                        _, html_path = html_schedule_path(
                            inst_name, n, inst_m, inst_c, inst_r_max, inst_R_max
                        )
                        refresh_globals()
                        if html_path.exists():
                            print(f"Skipping {inst_name} r={inst_r_max} R={inst_R_max} "
                                  f"(already in summary.csv and HTML exists)")
                            continue
                        print(f"Regenerating {inst_name} r={inst_r_max} R={inst_R_max} "
                              f"(summary exists, HTML missing)")
                    else:
                        print(f"Skipping {inst_name} r={inst_r_max} R={inst_R_max} "
                              f"(already in summary.csv)")
                        continue
                completed_runs.add(key)

                print(f"Running {inst_name} r={inst_r_max} R={inst_R_max}")
                run_single_instance(inst_name, inst_m, inst_c, inst_r_max, inst_R_max)

            except Exception as e:
                print(f"Error running {inst_name} r={inst_r_max} R={inst_R_max}: {e}")

    else:
        # Single instance mode: <instance_id> <r_max> <R_max>
        instance_id = int(sys.argv[1])
        r_max_param = int(sys.argv[2])
        R_max_param = int(sys.argv[3])

        current_data_set = test_data_set if is_test else data_set
        instance = current_data_set[instance_id]
        name_param = instance[0]
        m_param = instance[1]
        c_param = instance[2]

        run_single_instance(name_param, m_param, c_param, r_max_param, R_max_param)
