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
SCRIPT_NAME = Path(__file__).name
# Use absolute POSIX path for self-invocation under WSL
SCRIPT_PATH = Path(__file__).resolve().as_posix()
PROJECT_ROOT = Path(__file__).resolve().parent.parent
# Default to consolidated Output/{solver_name}
DEFAULT_OUTPUT_ROOT = PROJECT_ROOT / "Output" / Path(__file__).stem
OUTPUT_ROOT = Path(os.environ.get("OUTPUT_ROOT", str(DEFAULT_OUTPUT_ROOT)))
DATA_DIR = PROJECT_ROOT / "presedent_graph"
POWER_DIR = PROJECT_ROOT / "official_task_power"
var_map = {}
var_counter = 0

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

    # XLSX if pandas available
    try:
        import pandas as pd  # type: ignore

        df = pd.DataFrame(merged)
        xlsx_path = out_dir / "summary.xlsx"
        df.to_excel(xlsx_path, index=False)
    except Exception:
        pass

    summary_rows.clear()

def add_summary_row(status: str, peak: Any, attempts: int, runtime_sec: float, base_vars: int, base_clause_count: int):
    """Append a summary row and flush it to disk."""
    summary_rows.append(
        {
            "name": name,
            "n": n,
            "m": m,
            "c": c,
            "r_max": r_max,
            "R_max": R_max,
            "base_vars": base_vars,
            "base_clauses": base_clause_count,
            "peak": peak,
            "attempts": attempts,
            "runtime_sec": round(runtime_sec, 3),
            "status": status,
        }
    )
    flush_summary()

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
    global time_list, adj, neighbors, reversed_neighbors, W, X, S, A, R, n, m, c, r_max, R_max, var_map, var_counter, best_model, best_peak
    time_list = []
    adj = []
    neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    reversed_neighbors = [[0 for _ in range(1000)] for _ in range(1000)]
    W = []
    X = []
    S = []
    A = []
    R = []
    var_counter = 0
    var_map = {}
    

def read_input(name):
    cnt = 0
    global n, time_list, adj, neighbors, reversed_neighbors
    input_path = DATA_DIR / f"{name}.IN2"
    with input_path.open("r", encoding="utf-8") as f:
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
    power_path = POWER_DIR / f"{name}.txt"
    with power_path.open("r", encoding="utf-8") as f:
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

def get_key(value):
    for key, val in var_map:
        if (val == value):
            return key

def get_var(name, *args):
    global var_counter
    key = (name,) + args
    if key not in var_map:
        var_counter += 1
        var_map[key] = var_counter
    return var_map[key]

def set_var(value, name, *args):
    """Set a variable in the global var_map."""
    key = (name,) + args
    if value is not None:
        var_map[key] = value
    else:
        if key not in var_map:
            global var_counter
            var_counter += 1
            var_map[key] = var_counter
    return var_map[key]


def build_base_formula():
    """Build CNF for feasibility (all constraints except peak minimization)."""
    global var_counter
    horizon = c * r_max
    solver = Cadical195()
    var_counter = max_var_id()
    print("var_counter:", var_counter)
    base_clauses = []

    def emit(clause):
        base_clauses.append(clause)
        solver.add_clause(clause)

    # # Quick infeasibility: if any task longer than horizon, force UNSAT.
    # for task_id, duration in enumerate(time_list):
    #     if duration > horizon:
    #         emit([1, -1])
    #         return solver, var_counter, horizon, base_clauses

    valid_starts = []

    # (C3+C4) Tính valid_starts cho mỗi task (ALO/AMO S dùng staircase bên dưới)
    for j, tj in enumerate(time_list):
        latest_start = horizon - tj
        starts = [t for t in range(latest_start + 1)]
        valid_starts.append(starts)

    # (C1+C2) Staircase encoding cho X: ALO + AMO dùng biến phụ Y[j][k]
    # Y[j][k] = true  ⟺  task j được gán vào máy k hoặc nhỏ hơn
    for j in range(n):
        set_var(X[j][0], "Y", j, 0)
        for k in range(1, m - 1):
            emit([-get_var("Y", j, k-1), get_var("Y", j, k)])   # Y[j][k-1] → Y[j][k]
            emit([-X[j][k], get_var("Y", j, k)])                 # X[j][k] → Y[j][k]
            emit([-X[j][k], -get_var("Y", j, k-1)])              # X[j][k] → ¬Y[j][k-1]
            emit([X[j][k], get_var("Y", j, k-1), -get_var("Y", j, k)])  # Y[j][k] → Y[j][k-1] ∨ X[j][k]
        # Last machine
        emit([get_var("Y", j, m-2), X[j][m-1]])
        emit([-get_var("Y", j, m-2), -X[j][m-1]])
    print("After var: ", var_counter)

    # (C7) Precedence → machine order: nếu i ≺ j thì j không thể ở trạm sớm hơn i
    # Y[j][k] → ¬X[i][k+1]  ⟺  ¬Y[j][k] ∨ ¬X[i][k+1]
    for i, j in adj:
        for k in range(m - 1):
            emit([-get_var("Y", j, k), -X[i][k+1]])

    # (C3+C4) Staircase encoding cho S: ALO + AMO dùng biến phụ T[j][t]
    # T[j][t] = true  ⟺  task j bắt đầu tại thời điểm t hoặc sớm hơn (prefix sum)
    for j in range(n):
        last_t = horizon - time_list[j]  # thời điểm bắt đầu muộn nhất hợp lệ

        if last_t == 0:
            # Task chiếm toàn bộ horizon → chỉ có thể bắt đầu tại t=0
            emit([S[j][0]])
        else:
            # t=0: T[j][0] ≡ S[j][0]
            set_var(S[j][0], "T", j, 0)

            # t=1..last_t-1: staircase trung gian
            for t in range(1, last_t):
                emit([-get_var("T", j, t-1), get_var("T", j, t)])              # T[j][t-1] → T[j][t]
                emit([-S[j][t], get_var("T", j, t)])                            # S[j][t] → T[j][t]
                emit([-S[j][t], -get_var("T", j, t-1)])                         # S[j][t] → ¬T[j][t-1]
                emit([S[j][t], get_var("T", j, t-1), -get_var("T", j, t)])     # T[j][t] → T[j][t-1] ∨ S[j][t]

            # t=last_t: buộc phải có ít nhất một điểm bắt đầu
            emit([get_var("T", j, last_t-1), S[j][last_t]])
            emit([-get_var("T", j, last_t-1), -S[j][last_t]])


    # (C5) Hoạt động liên tục: S[j][t] → A[j][t], A[j][t+1], ..., A[j][t+tj-1]
    # Nếu task j bắt đầu tại t thì nó phải đang chạy trong suốt tj bước tiếp theo
    for j, tj in enumerate(time_list):
        for t in valid_starts[j]:
            for eps in range(tj):
                if t + eps < horizon:
                    emit([-S[j][t], A[j][t + eps]])

    # (C6a) Same-machine indicator — định nghĩa SM[i][j]:
    # (X[i][k] ∧ X[j][k]) → SM[i][j]  ⟺  ¬X[i][k] ∨ ¬X[j][k] ∨ SM[i][j]
    # Nếu cả i lẫn j cùng đặt trên máy k thì SM[i][j] = true
    for k in range(m):
        for i in range(n - 1):
            for j in range(i + 1, n):
                emit([-X[i][k], -X[j][k], get_var("SM", i, j)])

    # (C6b) Same-machine indicator — phủ định SM[i][j] khi khác máy:
    # (X[i][k] ∧ X[j][l]) → ¬SM[i][j]  (k ≠ l)  ⟺  ¬X[i][k] ∨ ¬X[j][l] ∨ ¬SM[i][j]
    # Nếu i và j ở hai máy khác nhau thì SM[i][j] = false
    for i in range(n - 1):
        for j in range(i + 1, n):
            for k in range(m):
                for l in range(m):
                    if k == l:
                        continue
                    emit([-X[i][k], -X[j][l], -get_var("SM", i, j)])

    # (C6c) Non-overlap khi cùng máy — dùng SM và staircase T:
    # Chiều 1 (ràng buộc j theo thời điểm bắt đầu của i):
    #   SM[i][j] ∧ S[i][t] → T[j][t - t_j] ∨ ¬T[j][t + t_i - 1]
    #   Nghĩa: nếu cùng máy và i bắt đầu tại t thì j phải kết thúc trước t (T[j][t-tj])
    #          hoặc j phải bắt đầu sau khi i kết thúc (¬T[j][t+ti-1])
    # Chiều 2 (đối xứng — ràng buộc i theo thời điểm bắt đầu của j):
    #   SM[i][j] ∧ S[j][t] → T[i][t - t_i] ∨ ¬T[i][t + t_j - 1]
    for i in range(n - 1):
        for j in range(i + 1, n):
            last_j = horizon - time_list[j]  # chỉ số T tối đa hợp lệ cho task j
            last_i = horizon - time_list[i]  # chỉ số T tối đa hợp lệ cho task i

            # Chiều 1: ràng buộc j theo start của i
            for t in range(horizon - time_list[i] + 1):
                max_t_j = last_j - 1
                clause = [-get_var("SM", i, j), -S[i][t]]
                t_left = t - time_list[j]          # j kết thúc trước t nếu T[j][t_left] = true
                if 0 <= t_left <= max_t_j:
                    clause.append(get_var("T", j, t_left))
                t_right = t + time_list[i] - 1    # j bắt đầu sau i kết thúc nếu ¬T[j][t_right]
                if 0 <= t_right <= max_t_j:
                    clause.append(-get_var("T", j, t_right))
                if len(clause) > 2:
                    emit(clause)

            # Chiều 2: ràng buộc i theo start của j (đối xứng)
            for t in range(horizon - time_list[j] + 1):
                max_t_i = last_i - 1
                clause = [-get_var("SM", i, j), -S[j][t]]
                t_left = t - time_list[i]          # i kết thúc trước t nếu T[i][t_left] = true
                if 0 <= t_left <= max_t_i:
                    clause.append(get_var("T", i, t_left))
                t_right = t + time_list[j] - 1    # i bắt đầu sau j kết thúc nếu ¬T[i][t_right]
                if 0 <= t_right <= max_t_i:
                    clause.append(-get_var("T", i, t_right))
                if len(clause) > 2:
                    emit(clause)

    # (C8) Precedence → time order: nếu i ≺ j và cùng máy k, thì i phải kết thúc trước j bắt đầu
    # Dùng staircase T để encode: ¬X[i][k] ∨ ¬X[j][k] ∨ ¬T[j][t] ∨ ¬S[i][t_i]
    # với t_i = t - t_i + 1 là thời điểm bắt đầu tương ứng của i để kết thúc đúng lúc t
    for i, j in adj:
        for k in range(m):
            left_bound = time_list[i] - 1           # j không thể bắt đầu trước t_i bước
            right_bound = horizon - time_list[j]    # giới hạn phải của T[j]

            # T[j][left_bound] phải là false (j chưa thể bắt đầu ở vị trí này)
            emit([-X[i][k], -X[j][k], -get_var("T", j, left_bound)])

            # Với t từ left_bound+1 đến right_bound-1
            for t in range(left_bound + 1, right_bound):
                t_i = t - time_list[i] + 1          # start của i để kết thúc tại t
                emit([-X[i][k], -X[j][k], -get_var("T", j, t), -S[i][t_i]])

            # T[j] đã đến cuối: ràng buộc S[i] không được bắt đầu quá muộn
            for t in range(max(0, right_bound - time_list[i] + 1), horizon - time_list[i] + 1):
                emit([-X[i][k], -X[j][k], -S[i][t], -get_var("T", j, horizon - time_list[j] - 1)])

    # (C9) Đơn điệu tài nguyên: R[k][r+1] → R[k][r]
    # Nếu máy k dùng tài nguyên thứ r+1 thì phải đã dùng tài nguyên thứ r
    for k in range(m):
        for r in range(r_max - 1):
            emit([-R[k][r + 1], R[k][r]])

    # (C10) Liên hệ cửa sổ khởi động với số tài nguyên máy:
    # S[j][t] ∧ X[j][k] → R[k][q-1]  với q = ⌈(t + t_j) / c⌉
    # Nếu task j bắt đầu tại t trên máy k thì máy k phải có đủ q tài nguyên
    for j, tj in enumerate(time_list):
        for k in range(m):
            for t in valid_starts[j]:
                q = math.ceil((t + tj) / c)
                if q <= r_max:
                    emit([-S[j][t], -X[j][k], R[k][q - 1]])
                else:
                    emit([-S[j][t], -X[j][k]])  # vô nghiệm: task không thể bắt đầu tại t

    # (C11) Ngân sách tài nguyên toàn tuyến: Σ R[k][r] ≤ R_max
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
    """Write an HTML table for the schedule to OUTPUT_ROOT/<instance>_mX_cY/rX_RY/."""
    if model is None:
        return None
    _, starts = build_schedule(model, horizon)
    compact = build_compact_table(model, horizon)
    res_counts = decode_resources(model)

    out_dir = OUTPUT_ROOT / f"{instance_name}_n{n}_m{m_val}_c{c_val}" / f"r{r_max_val}_R{R_max_val}"
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

def add_inagural(solver, peak):
    """Add INAGURAL constraints to the solver."""
    global var_counter, U, r_max, c, W, A, n, R_max
    horizon = c * r_max
    LB = max(W)
    UB = peak
    U = []

    # Ladder vars for bounds LB+1 .. UB-1 
    for _ in range(LB + 1, UB):
        U.append(var_counter + 1)
        var_counter += 1
    
    for i in range(1, len(U)):
        solver.add_clause([-U[i], U[i-1]])

    top_id = var_counter + 1
    for t in range(c):
        lits = []
        weights = []
        for u in U:
            lits.append(-u)
            weights.append(1)
        for i in range(n):
           lits.append(A[i][t])
           weights.append(W[i])

        if r_max >= 2:
            for i in range(n):
                lits.append(A[i][t+c])
                weights.append(W[i])
        if r_max >= 3:
            for i in range(n):
                lits.append(A[i][t+2*c])
                weights.append(W[i])
        
        enc = PBEnc.leq(lits=lits, weights=weights, bound=UB, top_id=top_id, encoding=EncType.binmerge)

        if enc.nv > var_counter:
            var_counter = enc.nv
            top_id = var_counter + 1
        for cl in enc.clauses:
            solver.add_clause(cl)
    return solver

def run_single_instance(name_param, m_param, c_param, r_max_param, R_max_param):
    print("run single instance")
    global name, m, c, r_max, R_max, X, S, A, R, best_model, best_peak, U
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
    print("Staircase 1 3")
    print(f"Solving {name} with m={m}, c={c}, r_max={r_max}, R_max={R_max}")
    t_start = time.time()
    solver, var_counter, horizon, base_clauses = build_base_formula()
    base_clause_count = len(base_clauses)

    add_summary_row(
        status="STARTED",
        peak="",
        attempts=0,
        runtime_sec=0.0,
        base_vars=var_counter,
        base_clause_count=base_clause_count,
    )

    # Initial solve for feasibility
    if not solver.solve():
        runtime = time.time() - t_start
        print("UNSAT or timed out")
        add_summary_row(
            status="TIMEOUT_INFEASIBLE",
            peak="",
            attempts=0,
            runtime_sec=runtime,
            base_vars=var_counter,
            base_clause_count=base_clause_count,
        )
        return

    model = solver.get_model()
    size = max(var_counter, max(abs(l) for l in model))
    first_peak, _ = compute_peak(decode_model(model, size), horizon)
    runtime_first = time.time() - t_start

    # Flush FEASIBLE immediately
    add_summary_row(
        status="FEASIBLE",
        peak=first_peak,
        attempts=0,
        runtime_sec=runtime_first,
        base_vars=var_counter,
        base_clause_count=base_clause_count,
    )

    # Tighten bound iteratively
    best_model = model
    best_peak = first_peak
    print("solver clauses:", solver.nof_clauses())
    solver = add_inagural(solver, best_peak)
    print("After INAGURAL, solver clauses:", solver.nof_clauses())

    attempts = 0
    LB = max(W)
    while True:
        attempts += 1
        if not solver.solve():
            break

        model = solver.get_model()
        # Flush INTERMEDIATE snapshot
        runtime_intermediate = time.time() - t_start
        size = max(var_counter, max(abs(l) for l in model))
        peak_found, _ = compute_peak(decode_model(model, size), horizon)
        add_summary_row(
            status="INTERMEDIATE",
            peak=peak_found,
            attempts=attempts,
            runtime_sec=runtime_intermediate,
            base_vars=var_counter,
            base_clause_count=base_clause_count,
        )
        outfile = write_html_schedule(
            name, m, c, r_max, R_max, model, horizon, peak_found, runtime_intermediate
        )
        if outfile:
            print(f"HTML schedule (intermediate) written to {outfile}")
        best_model = model
        best_peak = peak_found
        idx = best_peak - LB - 1
        print("New best peak:", best_peak)  
        if idx <= 0 or idx > len(U):
            break
        solver.add_clause([-U[idx - 1]])  # Exclude previous peak candidate

    runtime = time.time() - t_start
    print(f"Best peak: {best_peak} | runtime: {runtime:.3f}s")
    print(summarize_solution(best_model, horizon))
    outfile = write_html_schedule(name, m, c, r_max, R_max, best_model, horizon, best_peak, runtime)
    if outfile:
        print(f"HTML schedule written to {outfile}")

    # Final OPTIMAL snapshot (or best found)
    add_summary_row(
        status="OPTIMAL",
        peak=best_peak,
        attempts=attempts,
        runtime_sec=runtime,
        base_vars=var_counter,
        base_clause_count=base_clause_count,
    )


if __name__ == "__main__":
    # Detect if running in WSL
    is_wsl = os.path.exists('/proc/version') and 'microsoft' in open('/proc/version').read().lower()
    
    if len(sys.argv) == 1:
        print("Run all tests")
        TIMEOUT = 3600
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

        for instance_id in range(0, len(data_set)):
            instance = data_set[instance_id]
            name = instance[0]
            m = instance[1]
            c = instance[2]

            for r_max in range(1,4):
                for R_max in range(m, r_max * m + 1):
                    import shutil
                    use_wsl = False
                    if sys.platform != 'linux' and shutil.which("wsl"):
                        use_wsl = True

                    if use_wsl:
                        # On Windows, call WSL, quoting absolute script path
                        command = (
                            "wsl bash -c \"cd /mnt/c/Users/admin/Documents/Python/P3SAML3P && "
                            f"./runlim -r {TIMEOUT} .venv_wsl/bin/python '{SCRIPT_PATH}' {instance_id} {r_max} {R_max}\""
                        )
                    else:
                        # On Linux/macOS, run natively
                        runlim_path = PROJECT_ROOT / "runlim"
                        if runlim_path.exists():
                            try:
                                os.chmod(runlim_path, 0o755)
                            except Exception:
                                pass
                        command = (
                            f"cd '{PROJECT_ROOT}' && "
                            f"./runlim -r {TIMEOUT} '{sys.executable}' '{SCRIPT_PATH}' {instance_id} {r_max} {R_max}"
                        )

                    try:
                        key = (str(name), str(m), str(c), str(r_max), str(R_max))
                        if key in completed_runs:
                            print(f"Skipping instance {instance} {r_max} {R_max} (already in summary.csv)")
                            continue
                        completed_runs.add(key)

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
