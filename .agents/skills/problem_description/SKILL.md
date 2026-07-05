---
name: p3saml3p-problem-description
description: >
  Describes the P3SAML3P / SAML3P Assembly Line Balancing problem: variable
  definitions, constraint semantics, staircase encoding patterns, and
  common pitfalls. Use this skill whenever modifying solver constraints,
  adding new encodings, or debugging incorrect solutions.
---

# P3SAML3P — Problem & Code Description

## Problem Overview

**Assembly Line Balancing with Resource Constraints (SAT/ILP-based)**

Given `n` tasks with a precedence graph (DAG), assign each task to one of `m`
stations and determine its start time, such that:
- Precedence constraints are respected (on the same machine, predecessor finishes before successor starts)
- No two tasks overlap on the same machine at the same time
- Total resources do not exceed budget `R_max`
- **Objective**: minimize the **peak load** = max(Σ W[j] over all j running at time t)

## Key Parameters

| Symbol | Meaning |
|---|---|
| `n` | Number of tasks |
| `m` | Number of stations (machines) |
| `c` | Cycle time (real-time period) |
| `r_max` | Max resources per station |
| `R_max` | Total resource budget across all stations |
| `horizon` | `c × r_max` — total time horizon for scheduling |
| `t_j` / `time_list[j]` | Duration of task j |
| `W[j]` | Load weight of task j |
| `adj` | List of precedence pairs `(i, j)` meaning i ≺ j |

## Decision Variables

All variables are **SAT Boolean literals** (positive integer IDs). Negation is `-var`.

### Primary Variables (fixed IDs, defined in `generate_vars()`)

| Variable | Index | Meaning |
|---|---|---|
| `X[j][k]` | `j*m + k + 1` | Task j assigned to machine k |
| `S[j][t]` | offset formula | Task j **starts** at time t; domain `t ∈ [0, horizon-tj]` |
| `A[j][t]` | offset formula | Task j is **active (running)** at time t; domain `t ∈ [0, horizon-1]` |
| `R[k][r]` | offset formula | Machine k uses at least `r+1` resources (staircase) |

### Auxiliary Variables (created lazily via `get_var(name, *args)`)

| Variable | Key | Meaning |
|---|---|---|
| `Y[j][k]` | `("Y", j, k)` | Cumulative of X: "task j assigned to machine ≤ k" |
| `T[j][t]` | `("T", j, t)` | Cumulative of S: "task j starts at time ≤ t"; domain `t ∈ [0, horizon-tj-1]` |
| `SM[i][j]` | `("SM", i, j)` | Indicator: tasks i and j are on the **same machine** (IncrementalSM only) |

> [!IMPORTANT]
> `T[j][t]` domain is `[0, horizon-tj-1]`, NOT `[0, horizon-tj]`.
> The last slot `T[j][horizon-tj]` would always be TRUE (trivially), so it is NOT created.
> The constraint for the last slot uses `S[j][horizon-tj]` directly (staircase boundary clauses).

## Staircase Encoding Pattern

Both `Y` (for X) and `T` (for S) use the same **staircase (prefix sum) encoding**:

```
set_var(X[j][0], "Y", j, 0)              # Base: Y[j][0] = X[j][0]
for k in 1..m-2:
    Y[j][k-1] → Y[j][k]                 # Monotone
    X[j][k] → Y[j][k]                   # If assigned to k, set prefix
    X[j][k] → ¬Y[j][k-1]               # At-most-one
    Y[j][k] → Y[j][k-1] ∨ X[j][k]      # Definition
# Last slot: Y[j][m-2] ⊕ X[j][m-1]     # Exactly one
```

Same pattern for T (with S replacing X, and time index replacing machine index).

## Constraint Summary (C1–C11 + INAGURAL)

| Constraint | Clause form | Meaning |
|---|---|---|
| C1+C2 | Staircase on Y | Each task on exactly 1 machine |
| C3+C4 | Staircase on T | Each task has exactly 1 start time |
| C5 | `[-S[j][t], A[j][t+ε]]` for ε∈[0,tj) | Task runs continuously from start |
| C6 | `[-X[i][k], -X[j][k], -A[i][t], -A[j][t]]` | No two tasks on same machine at same time |
| C6a | `[-X[i][k], -X[j][k], SM[i][j]]` | SM=true if same machine |
| C6b | `[-X[i][k], -X[j][l], -SM[i][j]]` k≠l | SM=false if different machines |
| C6c | SM + T → no-overlap | No-overlap via T (IncrementalSM) |
| C7 | `[-Y[j][k], -X[i][k+1]]` for (i,j)∈adj | Predecessor not at a later station |
| C8 | T-based precedence (see below) | On same machine, i finishes before j starts |
| C9 | `[-R[k][r+1], R[k][r]]` | Resource monotonicity |
| C10 | `[-S[j][t], -X[j][k], R[k][q-1]]` | Start time → resource level activated |
| C11 | PBEnc ≤ R_max on all R[k][r] | Line-wide resource budget |
| INAGURAL | Ladder `U[i]` over time phases | Tightens peak bound in optimization loop |

## DOcplex ILP Formulation Notes

`solvers/CPLEX_ILP.py` implements the ILP equations directly with DOcplex
variables `X[j,k]`, `S[j,t]`, `R[k,r]`, and integer `W_M`. It should solve via
`mdl.solve(...)` using the native CPLEX Python API, not by exporting LP/SAV
files and shelling out to the `cplex` executable.

Critical equation/indexing notes:

- Eq. (5) station precedence and Eq. (8) same-station temporal precedence apply
  only to real precedence arcs `(i,j) ∈ adj`, not to every pair with `i < j`.
  Eq. (9) no-overlap is the one that applies to every unordered task pair.
- Eq. (7) resource activation is easy to shift by one. In 1-based math:
  `T^j_{r-1} = {0, ..., (r-1)c - t_j}`. In 0-based Python, for `R[k,r_idx]`,
  use `upper_t = r_idx * c - t_j`. If `upper_t < 0`, the constraint reduces to
  `X[j,k] <= R[k,r_idx]`.
- `R[k,r]` is a staircase variable: true means the station has at least `r+1`
  resources active. Keep Eq. (11) / C9 monotonicity `R[k,r+1] <= R[k,r]`.
- DOcplex progress data uses `pdata.current_objective` with
  `pdata.has_incumbent`; do not read `pdata.objective`.
- CPLEX ILP writes HTML schedules only when `--html` or `--write-html` is
  passed. In batch mode, if `summary.csv` already has an instance but the HTML
  file is missing, rerun that instance instead of skipping it.
- CPLEX ILP `attempts` means the number of incumbent objective improvements
  observed by the DOcplex progress listener; final rows should carry this
  count instead of always writing zero.
- For CPLEX Academic/Education installed in WSL, prefer the WSL venv at
  `/home/lucifong/P3SAML3P/.venv/bin/python3` and verify with:
  `python -c "import docplex, cplex; print(cplex.Cplex().get_version())"`.

## C8 Precedence Constraint — Detailed

For `(i,j) ∈ adj` (i must finish before j starts) on the same machine k:

```
left_bound  = ti - 1          # j cannot start before i could possibly finish
right_bound = horizon - tj    # last valid start of j
```

Three regions:

| Region | Clause | Meaning |
|---|---|---|
| **Head** `t = left_bound` | `[-X[i][k], -X[j][k], -T[j][left_bound]]` | j already started too early |
| **Middle** `t ∈ (left_bound, right_bound)` | `[-X[i][k], -X[j][k], -T[j][t], -S[i][t-ti+1]]` | j starts at ≤t while i starts at t-ti+1 |
| **Tail** `t ∈ [right_bound-ti+1, horizon-ti]` | `[-X[i][k], -X[j][k], -S[i][t]]` | i starts so late it violates regardless of j's start |

> [!WARNING]
> **TAIL REGION BUG (fixed)**: The original tail clause was:
> `[-X[i][k], -X[j][k], -S[i][t], -T[j][horizon-tj-1]]`
> This is **incorrect** — when j starts at its latest slot `horizon-tj`,
> `T[j][horizon-tj-1] = False` → clause becomes tautology (constraint vacuous).
> The case is actually covered by C6 (no-overlap), so the correct clause is simply:
> `[-X[i][k], -X[j][k], -S[i][t]]`
> **All solver files have been fixed with this correction.**

## Variable Domain Boundaries (Critical)

| Variable | Valid index range | Notes |
|---|---|---|
| `S[j][t]` | `t ∈ [0, horizon-tj]` | Inclusive, `horizon-tj+1` values |
| `T[j][t]` | `t ∈ [0, horizon-tj-1]` | `T[j][horizon-tj]` would be trivially TRUE — not created |
| `A[j][t]` | `t ∈ [0, horizon-1]` | All time slots |
| `X[j][k]` | `k ∈ [0, m-1]` | All machines |
| `Y[j][k]` | `k ∈ [0, m-2]` | `Y[j][m-1]` would be trivially TRUE — not created |
| `R[k][r]` | `r ∈ [0, r_max-1]` | Staircase: R[k][r]=True means ≥r+1 resources used |

## Key Relationships

- `T[j][t] = True` ↔ task j starts at some time `s ≤ t`
- `T[j][t] = False` ↔ task j starts at some time `s > t`
- `Y[j][k] = True` ↔ task j is assigned to some machine `k' ≤ k`
- `SM[i][j] = True` ↔ tasks i and j are on the same machine

## File Structure

```
P3SAML3P/
├── solvers/           # Main solver scripts
│   ├── base.py          # Baseline (A-var no-overlap)
│   ├── Atmostk.py       # AtMostK resource encoding
│   ├── Staircase13.py   # Staircase variant
│   ├── Incremental.py   # + C8 temporal tightening
│   ├── Inheritant.py    # + precedence inheritance
│   ├── IncrementalSM.py # SM encoding (no A vars in C6) ← LATEST
│   ├── maxsat.py        # RC2 MaxSAT
│   └── CPLEX_ILP.py     # DOcplex ILP formulation solved by native CPLEX API
├── presedent_graph/   # Input .IN2 files
├── official_task_power/ # Task weights .txt
├── runners/           # runlim wrapper scripts
└── Output/            # Auto-generated results
    └── <SolverName>/
        ├── summary.csv / summary.xlsx
        └── <instance>_n<n>_m<m>_c<c>/r<r>_R<R>/<...>.html
```

## Input Format (.IN2)

```
<n>           # number of tasks
<t_1>         # duration of task 1
...
<t_n>
<i>,<j>       # precedence edge i ≺ j (1-indexed)
...
-1,-1         # sentinel
```

## Running the Solvers

```bash
# Run full benchmark suite
/home/lucifong/P3SAML3P/.venv/bin/python3 solvers/Incremental.py --no-html

# Run single instance: <instance_id> <r_max> <R_max>
/home/lucifong/P3SAML3P/.venv/bin/python3 solvers/Incremental.py 0 1 6

# Attach to running screen
screen -r incremental
screen -r incrementalSM
```

## Common Pitfalls When Modifying Constraints

1. **T[j] index out of range**: `T[j][t]` only exists for `t ∈ [0, horizon-tj-1]`.
   Accessing `T[j][horizon-tj]` via `get_var` would create a spurious new variable, not a known one.

2. **Tail clause pattern**: See C8 tail region above — never use `T[j][horizon-tj-1]` as a substitute for "always true"; use `[-X[i][k], -X[j][k], -S[i][t]]` directly.

3. **`get_var` creates variables on first access**: If you call `get_var("T", j, t)` for a `t` outside the defined range, it will create a fresh unconstrained variable — silently breaking the model.

4. **`set_var` aliases variables**: `set_var(X[j][0], "Y", j, 0)` makes `Y[j][0]` point to the same SAT variable as `X[j][0]` — do not create separate variables for base cases.

5. **`horizon = c * r_max`**, not `c`. All time indices go up to `horizon`, not `c`.

6. **`--no-html` flag**: Pass `--no-html` to any solver to skip HTML schedule output (significantly faster for large runs).
