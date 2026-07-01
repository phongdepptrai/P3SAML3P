# P3SAML3P — SAT-based Assembly Line Balancing Solver

A project solving the **Assembly Line Balancing** problem with resource constraints, using various SAT/MaxSAT encoding strategies. Each solver version experiments with a different encoding approach to minimize the **peak load**.

---

## Table of Contents

- [Problem Description](#problem-description)
- [Installation \& Running](#installation--running)
- [Solver Versions Summary](#solver-versions-summary)
- [Constraint Descriptions](#constraint-descriptions)
- [Directory Structure](#directory-structure)
- [Output Format](#output-format)
- [Dataset](#dataset)

---

## Problem Description

Given a precedence graph consisting of `n` tasks with execution time `t_j`, each task needs to be assigned to one of `m` stations and its start time `S[j]` must be determined, such that:

- Precedence constraints `i ≺ j` are satisfied (task i finishes before task j starts if they are on the same machine).
- No two tasks overlap on the same machine.
- The total allocated resources do not exceed the budget `R_max`.
- **Minimize the peak load**: the maximum value of the sum of `W[j]` over all tasks j running at the same time slot.

**Parameters:**

| Symbol | Meaning |
|---|---|
| `n` | Number of tasks |
| `m` | Number of stations |
| `c` | Cycle time |
| `r_max` | Maximum resources per station |
| `R_max` | Total resources for the entire line |
| `W[j]` | Load weight of task j |
| `horizon` | Time horizon = `c × r_max` |

---

## Installation & Running

### 1. Create a virtual environment

```bash
python3 -m venv .venv
source .venv/bin/activate
pip install python-sat tabulate pandas openpyxl pypblib
```

### 2. Run via launcher (interactive solver selection menu)

```bash
source .venv/bin/activate
python run_launcher.py
```

### 3. Run a solver directly

```bash
# Run the entire test suite (batch)
python solvers/<SolverName>.py

# Run a specific instance: <instance_id> <r_max> <R_max>
python solvers/<SolverName>.py 0 1 6
```

### 4. Run via runner script (with runlim support)

```bash
python runners/<SolverName>_run.py
```

---

## Solver Versions Summary

| Version | File | No-Overlap Strategy (C6) | X/S Encoding | Intermediate log | Notes |
|---|---|---|---|---|---|
| **base** | `solvers/base.py` | 4-literal A vars: `[-X[i][k],-X[j][k],-A[i][t],-A[j][t]]` | Staircase Y + Staircase T | ✅ | Baseline version, simplest encoding |
| **Atmostk** | `solvers/Atmostk.py` | 4-literal A vars (same as base) | Staircase Y + Staircase T | ✅ | Adds AtMostK encoding for resources |
| **Staircase13** | `solvers/Staircase13.py` | 4-literal A vars | Staircase Y + Staircase T | ✅ | Staircase variant, named after the encoding |
| **Incremental** | `solvers/Incremental.py` | 4-literal A vars + C8 using T vars | Staircase Y + Staircase T | ✅ | Adds C8 tightening over time using T (prefix sum) |
| **Inheritant** | `solvers/Inheritant.py` | 4-literal A vars + C8 using T vars | Staircase Y + Staircase T | ✅ | Similar to Incremental, adds precedence inheritance constraints |
| **IncrementalSM** | `solvers/IncrementalSM.py` | **SM encoding** — auxiliary variables `SM[i][j]`, uses T vars instead of A vars | Staircase Y + Staircase T | ✅ | **Latest** — removes A vars from no-overlap |
| **maxsat** | `solvers/maxsat.py` | 4-literal A vars | Staircase Y + Staircase T | ❌ | Uses RC2 MaxSAT, no intermediate logging |

### Comparing C6 No-Overlap — Number of Clauses

| Version | Constraint | Complexity | Literal type |
|---|---|---|---|
| base / Atmostk / Staircase / Incremental / Inheritant / maxsat | `[-X[i][k], -X[j][k], -A[i][t], -A[j][t]]` | O(n² × m × horizon) | 4-literal |
| **IncrementalSM — C6a** | `[-X[i][k], -X[j][k], SM[i][j]]` | O(n² × m) | 3-literal |
| **IncrementalSM — C6b** | `[-X[i][k], -X[j][l], -SM[i][j]]` (k≠l) | O(n² × m²) | 3-literal |
| **IncrementalSM — C6c** | `[-SM[i][j], -S[i][t], ±T[j][...]]` (bidirectional) | O(n² × horizon) | 3-literal |

### Optimization Strategy

| Version | Strategy |
|---|---|
| base / Atmostk / Staircase / Incremental / Inheritant / IncrementalSM | Linear loop: gradually tightening bounds, using INAGURAL ladder vars `U[i]` |
| **maxsat** | Single call to RC2 MaxSAT (pysat) — direct optimization, no intermediate logging |

---

## Constraint Descriptions

| Name | Description |
|---|---|
| **C1+C2** | Staircase encoding for X (ALO+AMO): each task is assigned to exactly 1 machine, using auxiliary variables `Y[j][k]` |
| **C3+C4** | Staircase encoding for S (ALO+AMO): each task has exactly 1 start time, using auxiliary variables `T[j][t]` |
| **C5** | Continuity: `S[j][t] → A[j][t..t+tj-1]` — task runs continuously from start |
| **C6** | No-overlap (legacy solvers): two tasks on the same machine cannot run simultaneously, using A variables |
| **C6a** | SM indicator definition: `(X[i][k] ∧ X[j][k]) → SM[i][j]` |
| **C6b** | SM indicator negation: `(X[i][k] ∧ X[j][l]) → ¬SM[i][j]` with k≠l |
| **C6c** | No-overlap using SM+T: `SM[i][j] ∧ S[i][t] → T[j][t-tj] ∨ ¬T[j][t+ti-1]` (bidirectional) |
| **C7** | Precedence → machine order: `Y[j][k] → ¬X[i][k+1]` (if i≺j, then j cannot be at an earlier station than i) |
| **C8** | Precedence → temporal order: if i≺j on the same machine, i must finish before j starts (using T variables) |
| **C9** | Resource monotonicity: `R[k][r+1] → R[k][r]` |
| **C10** | Relation of start time to resources: `S[j][t] ∧ X[j][k] → R[k][q-1]` with q=⌈(t+tj)/c⌉ |
| **C11** | Line-wide resource budget: `Σ R[k][r] ≤ R_max` (PBEnc BinMerge) |
| **INAGURAL** | Ladder variables `U[i]` for each time phase, used to tighten peak bound in each loop iteration |

---

## Directory Structure

```
P3SAML3P/
├── README.md
├── run_launcher.py          # Solver selection menu and runner
├── generate_table.py        # Generates summary results table
├── validate_schedule.py     # Validates schedule correctness
├── runlim                   # Resource monitoring binary (Linux x86-64)
│
├── solvers/                 # Solver versions
│   ├── base.py
│   ├── Atmostk.py
│   ├── Staircase13.py
│   ├── Incremental.py
│   ├── Inheritant.py
│   ├── IncrementalSM.py     # SM encoding — latest version
│   └── maxsat.py
│
├── runners/                 # Wrapper scripts (runlim + Linux/WSL dual support)
│   ├── base_run.py
│   ├── Atmostk_run.py
│   ├── Staircase_run.py
│   ├── Incremental_run.py
│   ├── Inheritant_run.py
│   ├── IncrementalSM_run.py
│   └── maxsat_run.py
│
├── presedent_graph/         # Precedence graph input files (.IN2)
├── official_task_power/     # Task weight files (.txt)
└── Output/                  # Run output (auto-generated)
    └── <SolverName>/
        ├── summary.csv
        ├── summary.xlsx
        └── <instance>_n<n>_m<m>_c<c>/
            └── r<r>_R<R>/
                └── <instance>_..._r<r>_R<R>.html
```

---

## Output Format

### `summary.csv` / `summary.xlsx`

| Column | Meaning |
|---|---|
| `name` | Instance name |
| `n` / `m` / `c` | Number of tasks / stations / cycle time |
| `r_max` / `R_max` | Resource parameters |
| `base_vars` | Number of base SAT variables |
| `base_clauses` | Number of base SAT clauses |
| `peak` | Best peak load found |
| `attempts` | Number of optimization loops |
| `runtime_sec` | Running time (seconds) |
| `status` | `STARTED` / `FEASIBLE` / `INTERMEDIATE` / `OPTIMAL` / `TIMEOUT_INFEASIBLE` |

---

## Dataset

Instances from the standard SALBP dataset, run with `r_max ∈ {1,2,3}` and `R_max ∈ [m, r_max × m]`:

| ID | Name | m | c | Difficulty |
|---|---|---|---|---|
| 0 | MERTENS | 6 | 6 | Easy |
| 1 | MERTENS | 2 | 18 | Easy |
| 2 | BOWMAN | 5 | 20 | Easy |
| 3 | JAESCHKE | 8 | 6 | Easy |
| 4 | JAESCHKE | 3 | 18 | Easy |
| 5 | JACKSON | 8 | 7 | Easy |
| 6 | JACKSON | 3 | 21 | Easy |
| 7 | MANSOOR | 4 | 48 | Easy |
| 8 | MANSOOR | 2 | 94 | Easy |
| 9 | MITCHELL | 8 | 14 | Easy |
| 10 | MITCHELL | 3 | 39 | Easy |
| 11 | ROSZIEG | 10 | 14 | Easy |
| 12 | ROSZIEG | 4 | 32 | Easy |
| 13 | BUXEY | 14 | 25 | Hard |
| 14 | BUXEY | 7 | 47 | Hard |
| 15 | SAWYER | 14 | 25 | Hard |
| 16 | SAWYER | 7 | 47 | Hard |

---

## Dependencies

```
python-sat   # SAT solver (CaDiCaL195, RC2, PBEnc)
tabulate     # Terminal table formatting
pandas       # Excel export
openpyxl     # .xlsx writer engine
pypblib      # Pseudo-Boolean encoding (PBEnc)
```
