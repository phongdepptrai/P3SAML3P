# Copilot instructions for this repo

## Big picture
- This repo implements SAT/MaxSAT-based solvers for precedence-constrained scheduling. Each solver is a standalone script in `solvers/*.py` (e.g., `solvers/base.py`, `solvers/Incremental.py`, `solvers/IncreMaxsat.py`).
- Inputs are precedence graphs in `presedent_graph/*.IN2` and per-task power weights in `official_task_power/*.txt`. `read_input()` and `load_power()` in each solver read these.
- Core model variables are global matrices: `X` (task→machine), `S` (task start time), `A` (task active at time), `R` (machine resources). `generate_vars()` assigns contiguous variable IDs used by PySAT.
- Output is written under `Output/{SolverName}/<instance>_n{n}_m{m}_c{c}/r{r_max}_R{R_max}/` as HTML schedules plus `summary.csv`/`summary.xlsx` (see `write_html_schedule()` + `flush_summary()` in solvers).

## Critical workflows
- On Windows, run solvers via WSL wrappers in `runners/*_run.py` (they call `/mnt/c/.../.venv_wsl/bin/python` and optionally `runlim`). Use `run_launcher.py` for an interactive menu.
- To validate schedules, use `validate_schedule.py`, which reads HTML outputs and re-checks constraints against the `.IN2` inputs.
- To build summary tables from `summary.csv`, use `generate_table.py` (it emits `summary_table.html`).

## Project-specific conventions
- Solvers share the same global state layout; when adding constraints, update `var_counter`/`var_map` consistently and keep variable numbering contiguous with `generate_vars()` and `max_var_id()`.
- `summary.csv` is de-duplicated by key `(name, n, m, c, r_max, R_max)`; use `add_summary_row()` to record results.
- Output root can be overridden with `OUTPUT_ROOT` env var; default is `Output/{solver_name}`.

## External dependencies / integrations
- PySAT is the core SAT engine (`pysat.solvers.Cadical195`, `pysat.pb.PBEnc`). Some solvers use cardinality encodings (`pysat.card.CardEnc`).
- `solvers/IncreMaxsat.py` optionally calls a MaxHS binary (`MAXHS_BIN` env var) and has WSL path bridging via `to_wsl_path()`.
- `runlim` is used for time-limited batch runs when running via WSL in solver `__main__` blocks.

## Example entry points
- Single instance runs are in `run_single_instance()` within each solver; batch runs are triggered when the solver is executed with no CLI args.
- The dataset definition (`data_set`) drives which instances are run for batch mode.
