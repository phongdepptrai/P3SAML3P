from math import inf
import math
import re
import time
import signal
import json
import subprocess
import os

from datetime import datetime
from pathlib import Path

from pysat.solvers import Cadical195
import fileinput
from tabulate import tabulate
import webbrowser
import sys
from pysat.pb import PBEnc, EncType
import csv
from typing import List, Dict, Any

# Global variables
time_list = []
adj = []
neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
reversed_neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
X = []
A = []
S = []
R = []
W = []
best_model = None
best_peak = None
name = ""
m = 0
c = 0
r_max = 0
R_max = 0
n = 0
summary_rows: List[Dict[str, Any]] = []

def flush_summary():
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

    out_dir = Path("Output_html")
    out_dir.mkdir(exist_ok=True)
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

    # XLSX if pandas available
    try:
        import pandas as pd  # type: ignore

        df = pd.DataFrame(merged)
        xlsx_path = out_dir / "summary.xlsx"
        df.to_excel(xlsx_path, index=False)
    except Exception:
        pass

    summary_rows.clear()

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

def refresh_globals():
    global time_list, adj, neighbors, reversed_neighbors, W
    time_list = []
    adj = []
    neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    reversed_neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    W = []

def read_input(name):
    cnt = 0
    global n, time_list, adj, neighbors, reversed_neighbors
    with open('presedent_graph/' + name + '.IN2', 'r') as f:
        for line in f:
            line = line.strip()
            if line:
                if cnt == 0:
                    n = int(line)
                elif cnt <= n: 
                    time_list.append(int(line))
                else:
                    line = line.split(",")
                    if(line[0] != "-1" and line[1] != "-1"):
                        adj.append([int(line[0])-1, int(line[1])-1])
                        neighbors[int(line[0])-1][int(line[1])-1] = 1
                        reversed_neighbors[int(line[1])-1][int(line[0])-1] = 1
                    else:
                        break
                cnt = cnt + 1

def load_power(name):
    """Read task power values for the given instance name."""
    global W
    with open('official_task_power/' + name + '.txt', 'r') as f:
        W = [int(line.strip()) for line in f if line.strip()]

def max_var_id():
    """Return the current maximum variable id from X/S/A/R."""
    vals = []
    for mat in (X, S, A, R):
        if mat:
            vals.append(max(max(row) for row in mat))
    return max(vals) if vals else 0

def generate_vars():
    global X, S, A, R, n, m, c, r_max
    X = [[j*m+i+1 for i in range (m)] for j in range(n)]
    S = [[m*n + j*c*r_max + i + 1 for i in range (c*r_max)] for j in range(n)]
    A = [[m*n + r_max*c*n + j*c*r_max + i + 1 for i in range (c*r_max)] for j in range(n)]
    R = [[m*n + r_max*c*n + c*r_max*n + k*r_max + i + 1 for i in range (r_max)] for k in range(m)]

def build_base_formula():
    """Build CNF for feasibility (all constraints except peak minimization)."""
    horizon = c * r_max
    solver = Cadical195()
    var_counter = max_var_id()
    base_clauses = []

    def emit(clause):
        base_clauses.append(clause)
        solver.add_clause(clause)

    # Quick infeasibility: if any task longer than horizon, force UNSAT.
    for task_id, duration in enumerate(time_list):
        if duration > horizon:
            emit([1, -1])
            return solver, var_counter, horizon, base_clauses

    valid_starts = []

    # (C1) ALO cho X
    for j in range(n):
        emit([X[j][k] for k in range(m)])

    # (C2) AMO cho X
    for j in range(n):
        for k1 in range(m):
            for k2 in range(k1 + 1, m):
                emit([-X[j][k1], -X[j][k2]])

    # (C3) ALO cho S và (C4) AMO cho S
    for j, tj in enumerate(time_list):
        latest_start = horizon - tj
        starts = [t for t in range(latest_start + 1)]
        valid_starts.append(starts)
        emit([S[j][t] for t in starts])
        for t1 in range(len(starts)):
            for t2 in range(t1 + 1, len(starts)):
                emit([-S[j][starts[t1]], -S[j][starts[t2]]])

    # (C5) Nếu khởi động thì phải đang chạy đủ tj bước
    for j, tj in enumerate(time_list):
        for t in valid_starts[j]:
            for eps in range(tj):
                if t + eps < horizon:
                    emit([-S[j][t], A[j][t + eps]])

    # (C6) Không chồng lấn trên cùng máy
    for i in range(n - 1):
        for j in range(i + 1, n):
            for k in range(m):
                for t in range(horizon):
                    emit([-X[i][k], -X[j][k], -A[i][t], -A[j][t]])

    # (C7) Nếu i ≺ j thì j không thể ở trạm sớm hơn i
    for i, j in adj:
        for k in range(m):
            for h in range(k + 1, m):
                emit([-X[j][k], -X[i][h]])

    # (C8) Trong cùng máy thì i không được bắt đầu sau j
    for i, j in adj:
        for k in range(m):
            for t1 in valid_starts[i]:
                for t2 in valid_starts[j]:
                    if t1 > t2:
                        emit([-X[i][k], -X[j][k], -S[i][t1], -S[j][t2]])

    # (C9) Nếu dùng tài nguyên r+1 thì phải dùng r
    for k in range(m):
        for r in range(r_max - 1):
            emit([-R[k][r + 1], R[k][r]])

    # (C10) Liên hệ cửa sổ khởi động với số tài nguyên máy
    for j, tj in enumerate(time_list):
        for k in range(m):
            for t in valid_starts[j]:
                q = math.ceil((t + tj) / c)
                if q <= r_max:
                    emit([-S[j][t], -X[j][k], R[k][q - 1]])
                else:
                    emit([-S[j][t], -X[j][k]])

    # (C11) Ngân sách tài nguyên toàn tuyến
    lits = []
    weights = []
    for k in range(m):
        for r in range(r_max):
            lits.append(R[k][r])
            weights.append(1)
    enc = PBEnc.leq(lits=lits, weights=weights, bound=R_max, top_id=var_counter, encoding=EncType.binmerge)
    for cl in enc.clauses:
        emit(cl)
    var_counter = max(var_counter, enc.nv)

    return solver, var_counter, horizon, base_clauses

def decode_model(model, size):
    """Convert model list to boolean array indexed by var id."""
    assign = [False] * (size + 1)
    for lit in model:
        if lit > 0 and lit <= size:
            assign[lit] = True
    return assign

def decode_resources(model):
    """Return list of resource counts per machine from model assignment."""
    size = max(max_var_id(), max(abs(l) for l in model))
    assign = decode_model(model, size)
    res_counts = []
    for k in range(m):
        used = 0
        for r in range(r_max):
            if assign[R[k][r]]:
                used = r + 1  # r is 0-based but represents resource r+1
        res_counts.append(used)
    return res_counts

def compute_peak(assign, horizon):
    """Compute peak load per real-time phase."""
    loads = [0 for _ in range(c)]
    for j in range(n):
        wj = W[j] if j < len(W) else 0
        for t in range(horizon):
            if assign[A[j][t]]:
                tau = t % c
                loads[tau] += wj
    peak = max(loads) if loads else 0
    return peak, loads

def add_peak_constraints(solver, bound, var_counter, horizon):
    """Add PB constraints: for each real-time phase tau, load <= bound."""
    for tau in range(c):
        lits = []
        weights = []
        for j in range(n):
            wj = W[j] if j < len(W) else 0
            for q in range(r_max):
                t = tau + q * c
                if t < horizon:
                    lits.append(A[j][t])
                    weights.append(wj)
        enc = PBEnc.leq(lits=lits, weights=weights, bound=bound, top_id=var_counter, encoding=EncType.binmerge)
        for cl in enc.clauses:
            solver.add_clause(cl)
        var_counter = max(var_counter, enc.nv)
    return var_counter

def summarize_solution(model, horizon):
    if model is None:
        return "UNSAT"
    size = max(max_var_id(), max(abs(l) for l in model))
    assign = decode_model(model, size)
    rows = []
    for j in range(n):
        machine = next((k for k in range(m) if assign[X[j][k]]), -1)
        start_time = next((t for t in range(horizon) if assign[S[j][t]]), -1)
        rows.append((j, machine, start_time))
    lines = [f"task {j+1}: machine {machine+1 if machine>=0 else '?'} start {start}" for j, machine, start in rows]
    return "\n".join(lines)

def build_schedule(model, horizon):
    """Return (table, starts) from model; table[machine][time] = task_id+1 or 0."""
    size = max(max_var_id(), max(abs(l) for l in model))
    assign = decode_model(model, size)
    table = [[0 for _ in range(horizon)] for _ in range(m)]
    starts = []
    for j in range(n):
        machine = next((k for k in range(m) if assign[X[j][k]]), -1)
        start_time = next((t for t in range(horizon) if assign[S[j][t]]), -1)
        starts.append((j, machine, start_time))
        if machine >= 0 and start_time >= 0:
            for t in range(start_time, min(start_time + time_list[j], horizon)):
                table[machine][t] = j + 1
    return table, starts

def build_compact_table(model, horizon):
    """Return per-machine resource rows (r_max rows, c cols) derived from starts."""
    size = max(max_var_id(), max(abs(l) for l in model))
    assign = decode_model(model, size)
    tables = []
    for k in range(m):
        machine_rows = [[0 for _ in range(c)] for _ in range(r_max)]
        for j in range(n):
            if not assign[X[j][k]]:
                continue
            start_time = next((t for t in range(horizon) if assign[S[j][t]]), -1)
            if start_time < 0:
                continue
            duration = time_list[j]
            for off in range(duration):
                t_abs = start_time + off
                row = t_abs // c
                col = t_abs % c
                if 0 <= row < r_max:
                    machine_rows[row][col] = j + 1
        tables.append(machine_rows)
    return tables

def write_html_schedule(instance_name, m_val, c_val, r_max_val, R_max_val, model, horizon, peak, runtime_sec):
    """Write an HTML table for the schedule to Output_html/<instance>_mX_cY/rX_RY/."""
    if model is None:
        return None
    _, starts = build_schedule(model, horizon)
    compact = build_compact_table(model, horizon)
    res_counts = decode_resources(model)

    out_dir = Path("Output_html") / f"{instance_name}_n{n}_m{m_val}_c{c_val}" / f"r{r_max_val}_R{R_max_val}"
    out_dir.mkdir(parents=True, exist_ok=True)
    outfile = out_dir / f"{instance_name}_n{n}_m{m_val}_c{c_val}_r{r_max_val}_R{R_max_val}.html"
    if outfile.exists():
        outfile.unlink()

    header_cells = "".join([f"<th>t{t}</th>" for t in range(c)])
    rows_html = []
    for k in range(m):
        rows_html.append(f"<tr class='machine'><th colspan='{c+1}'>Machine {k+1} (r={res_counts[k]})</th></tr>")
        rows_html.append(f"<tr><th></th>{header_cells}</tr>")
        for r in range(r_max):
            cells = "".join([f"<td>{compact[k][r][t] if compact[k][r][t] else ''}</td>" for t in range(c)])
            rows_html.append(f"<tr><th>Res {r+1}</th>{cells}</tr>")

    starts_text = "<br>".join(
        [f"Task {j+1}: machine {mach+1 if mach>=0 else '?'} start {st}" for j, mach, st in starts]
    )
    resources_text = "<br>".join([f"Machine {k+1}: {res_counts[k]} resources" for k in range(m)])

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

def run_single_instance(name_param, m_param, c_param, r_max_param, R_max_param):
    global name, m, c, r_max, R_max, X, S, A, R, best_model, best_peak
    name = name_param
    m = m_param
    c = c_param
    r_max = r_max_param
    R_max = R_max_param
    best_model = None
    best_peak = None
    
    refresh_globals()
    read_input(name)
    load_power(name)
    generate_vars()

    print(f"Solving {name} with m={m}, c={c}, r_max={r_max}, R_max={R_max}")
    t_start = time.time()
    solver, var_counter, horizon, base_clauses = build_base_formula()
    # Record STARTED marker
    summary_rows.append(
        {
            "name": name,
            "n": n,
            "m": m,
            "c": c,
            "r_max": r_max,
            "R_max": R_max,
            "base_vars": var_counter,
            "base_clauses": len(base_clauses),
            "peak": "",
            "attempts": 0,
            "runtime_sec": 0.0,
            "status": "STARTED",
        }
    )
    flush_summary()

    # Initial solve for feasibility
    if not solver.solve():
        runtime = time.time() - t_start
        print("UNSAT or timed out")
        summary_rows.append(
            {
                "name": name,
                "n": n,
                "m": m,
                "c": c,
                "r_max": r_max,
                "R_max": R_max,
                "base_vars": var_counter,
                "base_clauses": len(base_clauses),
                "peak": "",
                "attempts": 0,
                "runtime_sec": round(runtime, 3),
                "status": "TIMEOUT_INFEASIBLE",
            }
        )
        flush_summary()
        return

    model = solver.get_model()
    size = max(var_counter, max(abs(l) for l in model))
    first_peak, _ = compute_peak(decode_model(model, size), horizon)
    runtime_first = time.time() - t_start

    # Flush FEASIBLE immediately
    summary_rows.append(
        {
            "name": name,
            "n": n,
            "m": m,
            "c": c,
            "r_max": r_max,
            "R_max": R_max,
            "base_vars": var_counter,
            "base_clauses": len(base_clauses),
            "peak": first_peak,
            "attempts": 0,
            "runtime_sec": round(runtime_first, 3),
            "status": "FEASIBLE",
        }
    )
    flush_summary()

    # Tighten bound iteratively
    best_model = model
    best_peak = first_peak
    attempts = 0
    bound = first_peak - 1
    while bound >= 0:
        attempts += 1
        fresh_solver = Cadical195()
        for cl in base_clauses:
            fresh_solver.add_clause(cl)
        fresh_var_counter = add_peak_constraints(fresh_solver, bound, var_counter, horizon)

        if not fresh_solver.solve():
            break

        model = fresh_solver.get_model()
        size = max(fresh_var_counter, max(abs(l) for l in model))
        peak_found, _ = compute_peak(decode_model(model, size), horizon)
        best_model = model
        best_peak = peak_found
        bound = peak_found - 1

    runtime = time.time() - t_start
    print(f"Best peak: {best_peak} | runtime: {runtime:.3f}s")
    print(summarize_solution(best_model, horizon))
    outfile = write_html_schedule(name, m, c, r_max, R_max, best_model, horizon, best_peak, runtime)
    if outfile:
        print(f"HTML schedule written to {outfile}")

    # Final OPTIMAL snapshot (or best found)
    summary_rows.append(
        {
            "name": name,
            "n": n,
            "m": m,
            "c": c,
            "r_max": r_max,
            "R_max": R_max,
            "base_vars": var_counter,
            "base_clauses": len(base_clauses),
            "peak": best_peak,
            "attempts": attempts,
            "runtime_sec": round(runtime, 3),
            "status": "OPTIMAL",
        }
    )
    flush_summary()


if __name__ == "__main__":
    # Detect if running in WSL
    is_wsl = os.path.exists('/proc/version') and 'microsoft' in open('/proc/version').read().lower()
    
    if len(sys.argv) == 1:
        print("Run all tests")
        TIMEOUT = 3600

        for instance_id in range(0, len(data_set)):
            instance = data_set[instance_id]
            name = instance[0]
            m = instance[1]
            c = instance[2]

            for r_max in range(1,4):
                for R_max in range(m, r_max * m + 1):
                    if is_wsl:
                        # Already in WSL, run directly
                        command = f'cd /mnt/c/Users/admin/Documents/Python/P3SAML3P && ./runlim -r {TIMEOUT} .venv_wsl/bin/python test.py {instance_id} {r_max} {R_max}'
                    else:
                        # On Windows, call WSL
                        command = f'wsl bash -c "cd /mnt/c/Users/admin/Documents/Python/P3SAML3P && ./runlim -r {TIMEOUT} .venv_wsl/bin/python test.py {instance_id} {r_max} {R_max}"'

                    try:
                        print(f"Running instance {instance} {r_max} {R_max}")
                        process = subprocess.Popen(command, shell=True)
                        process.wait()
                        time.sleep(1)

                        result = None

                    except Exception as e:
                        print(f"Error running instance {instance} {r_max} {R_max}: {str(e)}")
    
    else:
        instance_id = int(sys.argv[1])
        r_max_param = int(sys.argv[2])
        R_max_param = int(sys.argv[3])

        instance = data_set[instance_id]
        name_param = instance[0]
        m_param = instance[1]
        c_param = instance[2]

        run_single_instance(name_param, m_param, c_param, r_max_param, R_max_param)
