"""
Validate schedules produced by test.py HTML output files.

Usage:
    python validate_schedule.py  # interactive: pick solver -> choose run-all or single -> pick instance if needed
    python validate_schedule.py Output/Staircase13/MERTENS_n7_m6_c6/r3_R6/MERTENS_n7_m6_c6_r3_R6.html

Checks:
    - Each task has a machine and start within horizon.
    - Start window vs resources: ceil((t + dur) / c) <= r_k.
    - Non-overlap on each machine in the virtual horizon (length = r_max * c).
    - Capacity per machine: sum(duration) <= c * r_k.
    - Resource counts: r_k <= r_max, sum r_k <= R_max.
    - Precedence: machine(j) >= machine(i); if same machine then start_i <= start_j.
"""

from __future__ import annotations

import argparse
import re
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple


def find_solver_dirs() -> List[Path]:
    """Return available solver output folders under Output/ (or legacy Output_*)."""
    solver_dirs: set[Path] = set()

    output_root = Path("Output")
    if output_root.exists():
        for child in output_root.iterdir():
            if child.is_dir():
                solver_dirs.add(child)

    for legacy in Path(".").glob("Output_*"):
        if legacy.is_dir():
            solver_dirs.add(legacy)

    return sorted(solver_dirs)


def find_html_outputs_for_solver(solver_dir: Path) -> List[Path]:
    """Find schedule HTML files for a given solver directory, excluding summary tables."""
    candidates: List[Path] = []
    for html_file in solver_dir.rglob("*.html"):
        if "summary" in html_file.name.lower():
            continue
        candidates.append(html_file)
    return sorted(candidates)


def prompt_choose(options: List[Path]) -> Path:
    """Prompt user to select a path; default is first."""
    print("Detected schedule outputs:")
    for idx, opt in enumerate(options, start=1):
        print(f"[{idx}] {opt}")
    choice = input(f"Select HTML [1-{len(options)}] (default 1): ").strip()
    if not choice:
        return options[0]
    try:
        idx = int(choice)
    except ValueError:
        raise SystemExit("Invalid selection.")
    if idx < 1 or idx > len(options):
        raise SystemExit("Selection out of range.")
    return options[idx - 1]


def prompt_choose_solver(solver_dirs: List[Path]) -> Path:
    """Prompt user to select which solver output to validate."""
    print("Available solver outputs:")
    for idx, solver in enumerate(solver_dirs, start=1):
        print(f"[{idx}] {solver.name} ({solver})")
    choice = input(f"Select solver [1-{len(solver_dirs)}] (default 1): ").strip()
    if not choice:
        return solver_dirs[0]
    try:
        idx = int(choice)
    except ValueError:
        raise SystemExit("Invalid solver selection.")
    if idx < 1 or idx > len(solver_dirs):
        raise SystemExit("Solver selection out of range.")
    return solver_dirs[idx - 1]


def prompt_run_mode() -> str:
    """Prompt for whether to validate all instances or a single one."""
    print("Validation mode:")
    print("[1] Validate all instances for this solver")
    print("[2] Validate a single instance")
    choice = input("Choose mode [1-2] (default 1): ").strip()
    if not choice or choice == "1":
        return "all"
    if choice == "2":
        return "single"
    raise SystemExit("Invalid mode selection.")


@dataclass
class InstanceData:
    name: str
    n: int
    m: int
    c: int
    r_max: int
    R_max: int
    durations: List[int]
    edges: List[Tuple[int, int]]
    res_counts: List[int]
    starts: List[Tuple[int, int]]  # (machine, start)


def parse_meta(html: str) -> Tuple[str, int, int, int, int]:
    """Extract instance, m, c, r_max, R_max from the meta block."""
    inst_match = re.search(r"Instance:</strong>\s*([^<&]+)", html)
    m_match = re.search(r"<strong>m:</strong>\s*([0-9]+)", html)
    c_match = re.search(r"<strong>c:</strong>\s*([0-9]+)", html)
    rmax_match = re.search(r"<strong>r_max:</strong>\s*([0-9]+)", html)
    Rmax_match = re.search(r"<strong>R_max:</strong>\s*([0-9]+)", html)
    if not (inst_match and m_match and c_match and rmax_match and Rmax_match):
        raise ValueError("Cannot parse meta information (instance/m/c/r_max/R_max)")
    return (
        inst_match.group(1).strip(),
        int(m_match.group(1)),
        int(c_match.group(1)),
        int(rmax_match.group(1)),
        int(Rmax_match.group(1)),
    )


def parse_resources(html: str, m: int) -> List[int]:
    res_lines = re.findall(r"Machine\s+([0-9]+):\s*([0-9]+)\s*resources", html)
    res = [0 for _ in range(m)]
    for mach_str, cnt_str in res_lines:
        idx = int(mach_str) - 1
        if 0 <= idx < m:
            res[idx] = int(cnt_str)
    return res


def parse_starts(html: str, n_hint: int | None = None) -> List[Tuple[int, int]]:
    starts = []
    for task_str, mach_str, start_str in re.findall(
        r"Task\s+([0-9]+):\s*machine\s*([0-9?]+)\s*start\s*([-0-9?]+)", html
    ):
        task_id = int(task_str) - 1
        if mach_str == "?":
            machine = -1
        else:
            machine = int(mach_str) - 1
        start = int(start_str) if start_str != "?" else -1
        starts.append((task_id, machine, start))
    if n_hint is not None and len(starts) < n_hint:
        # Pad missing with invalid entries
        for j in range(n_hint):
            if not any(t == j for t, _, _ in starts):
                starts.append((j, -1, -1))
    starts.sort(key=lambda x: x[0])
    return [(m, s) for _, m, s in starts]


def read_instance(instance_name: str) -> Tuple[int, List[int], List[Tuple[int, int]]]:
    path = Path("presedent_graph") / f"{instance_name}.IN2"
    if not path.exists():
        raise FileNotFoundError(f"Cannot find {path}")
    lines = [ln.strip() for ln in path.read_text().splitlines() if ln.strip()]
    n = int(lines[0])
    durations = [int(x) for x in lines[1 : n + 1]]
    edges: List[Tuple[int, int]] = []
    for ln in lines[n + 1 :]:
        a, b = ln.split(",")
        if a == "-1" or b == "-1":
            break
        edges.append((int(a) - 1, int(b) - 1))
    return n, durations, edges


def validate(data: InstanceData) -> List[str]:
    errors: List[str] = []
    horizon = data.c * data.r_max

    if len(data.starts) != data.n:
        errors.append(f"Expected {data.n} tasks in starts, got {len(data.starts)}")

    # Resource counts validity
    if any(r > data.r_max for r in data.res_counts):
        errors.append("Some machine has resources > r_max")
    if sum(data.res_counts) > data.R_max:
        errors.append("Total resources exceed R_max")

    # Capacity per machine and task placement checks
    machine_load = [0 for _ in range(data.m)]
    timeline = [[-1 for _ in range(horizon)] for _ in range(data.m)]

    for j, (mach, start) in enumerate(data.starts):
        if mach < 0 or mach >= data.m:
            errors.append(f"Task {j+1}: invalid machine {mach}")
            continue
        if start < 0:
            errors.append(f"Task {j+1}: invalid start {start}")
            continue
        dur = data.durations[j]
        if start + dur > horizon:
            errors.append(f"Task {j+1}: exceeds horizon (start {start}, dur {dur})")
        q = (start + dur + data.c - 1) // data.c
        if q > data.res_counts[mach]:
            errors.append(
                f"Task {j+1}: needs {q} resources on machine {mach+1}, available {data.res_counts[mach]}"
            )
        machine_load[mach] += dur
        for t in range(start, min(start + dur, horizon)):
            if timeline[mach][t] != -1:
                errors.append(
                    f"Overlap on machine {mach+1} at t={t}: tasks {timeline[mach][t]+1} and {j+1}"
                )
            else:
                timeline[mach][t] = j

    for k in range(data.m):
        if machine_load[k] > data.c * data.res_counts[k]:
            errors.append(
                f"Machine {k+1}: load {machine_load[k]} > c*r_k ({data.c}*{data.res_counts[k]})"
            )

    # Precedence: machine order and same-machine start order
    for i, j in data.edges:
        mach_i, start_i = data.starts[i]
        mach_j, start_j = data.starts[j]
        if mach_j < mach_i:
            errors.append(
                f"Precedence {i+1}->{j+1}: machine_j ({mach_j+1}) earlier than machine_i ({mach_i+1})"
            )
        if mach_i == mach_j and start_i > start_j:
            errors.append(
                f"Precedence {i+1}->{j+1}: same machine {mach_i+1} but start_i={start_i} > start_j={start_j}"
            )

    return errors


def validate_html_file(html_path: Path) -> Tuple[str, List[str]]:
    """Read an HTML schedule and return instance name with validation errors (empty if valid)."""
    html = html_path.read_text(encoding="utf-8")

    instance, m, c, r_max, R_max = parse_meta(html)
    n, durations, edges = read_instance(instance)
    res_counts = parse_resources(html, m)
    starts = parse_starts(html, n_hint=n)

    data = InstanceData(
        name=instance,
        n=n,
        m=m,
        c=c,
        r_max=r_max,
        R_max=R_max,
        durations=durations,
        edges=edges,
        res_counts=res_counts,
        starts=starts,
    )
    return instance, validate(data)


def main():
    parser = argparse.ArgumentParser(description="Validate schedule HTML from test.py output.")
    parser.add_argument(
        "html_file",
        nargs="?",
        help="Path to HTML output file from test.py",
    )
    parser.add_argument(
        "--auto",
        action="store_true",
        help="Auto-detect schedule HTML files in Output/* (or legacy Output_*) and prompt for selection (default when no html_file is given)",
    )
    args = parser.parse_args()

    html_paths: List[Path]
    if args.html_file:
        html_paths = [Path(args.html_file)]
    else:
        solver_dirs = find_solver_dirs()
        if not solver_dirs:
            raise SystemExit("No solver outputs found under Output/ or Output_*.")
        solver_dir = prompt_choose_solver(solver_dirs)

        candidates = find_html_outputs_for_solver(solver_dir)
        if not candidates:
            raise SystemExit(f"No schedule HTML files found under {solver_dir}.")

        mode = prompt_run_mode()
        if mode == "single":
            html_paths = [prompt_choose(candidates)]
            print(f"Selected: {html_paths[0]}")
        else:
            html_paths = candidates
            print(f"Validating all {len(html_paths)} schedules under {solver_dir}")

    multi_run = len(html_paths) > 1
    if not multi_run:
        html_path = html_paths[0]
        print(f"Validating {html_path}")
        instance, errs = validate_html_file(html_path)
        if not errs:
            print(f"VALID: schedule satisfies constraints for {instance}")
        else:
            print(f"INVALID ({len(errs)} issues) for {instance}:")
            for e in errs:
                print(f"- {e}")
        return

    # Multi-file run: only print details for invalid ones, summarize valids.
    invalid_results: List[Tuple[Path, str, List[str]]] = []
    valid_count = 0

    for html_path in html_paths:
        try:
            instance, errs = validate_html_file(html_path)
        except Exception as exc:  # keep going even if one file is broken
            errs = [f"Failed to validate: {exc}"]
            instance = html_path.stem

        if errs:
            invalid_results.append((html_path, instance, errs))
        else:
            valid_count += 1

    if invalid_results:
        print("\nInvalid schedules:")
        for html_path, instance, errs in invalid_results:
            print(f"\n--- {html_path} ({instance}) ---")
            print(f"{len(errs)} issue(s):")
            for e in errs:
                print(f"- {e}")
    else:
        print("\nNo invalid schedules found.")

    print(
        f"\nFinished {len(html_paths)} files: {valid_count} valid, {len(invalid_results)} invalid."
    )


if __name__ == "__main__":
    main()
