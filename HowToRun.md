# How to Run Solvers (WSL Environment)

Since compiling the SAT solvers natively on Windows can be complex, it is recommended to run the project using the WSL virtual environment.

## 1. Run a Solver Directly (WSL)

To run a solver on a single instance:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 solvers/<SolverName>.py <instance_id> <r_max> <R_max>
```
Example (HTML schedule output is **disabled** by default):
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 solvers/Incremental.py 0 1 6 --test
```

### Enable HTML Schedule Output
To generate and write HTML schedules to disk, add the `--html` or `--write-html` flag:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 solvers/Incremental.py 0 1 6 --test --html
```

## 2. Run All Test Instances (WSL)

To run all test instances in the benchmark test suite:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 solvers/<SolverName>.py --test
```
Example:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 solvers/Incremental.py --test
```

## 3. Run Interactive Launcher (WSL)

To launch the interactive solver selection menu:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 run_launcher.py
```
If you want to pass flags like `--html` or `--test` through the launcher, append them after `--`:
```bash
wsl /mnt/c/Users/admin/Documents/Python/P3SAML3P/.venv_wsl/bin/python3 run_launcher.py -- --html --test
```

## 4. Run CPLEX ILP with DOcplex

The CPLEX ILP solver uses DOcplex and the native CPLEX Python API. Use the
dedicated runner so the project is synced into WSL and executed with the WSL
virtual environment that has `docplex` and `cplex` installed:

```bash
python runners/CPLEX_ILP_run.py --test 0 3 10
```

To also write the HTML schedule:

```bash
python runners/CPLEX_ILP_run.py --html --test 0 3 10
```

From inside WSL, the equivalent direct command is:

```bash
/home/lucifong/P3SAML3P/.venv/bin/python3 solvers/CPLEX_ILP.py --test 0 3 10
```

To verify the DOcplex/CPLEX environment:

```bash
/home/lucifong/P3SAML3P/.venv/bin/python3 -c "import docplex, cplex; print(cplex.Cplex().get_version())"
```

## 5. Run CPLEX MSxLSPSC/MS04

Use the dedicated runner for the standalone Section 4 matheuristic:

```bash
python runners/CPLEX_msls_run.py 0 3 10 --test --ms-time-limit 600 --seed 42
```

To also write the HTML schedule:

```bash
python runners/CPLEX_msls_run.py 0 3 10 --test --ms-time-limit 600 --seed 42 --html
```
tmux -S /home/lucifong/P3SAML3P/.tmux/ok.sock attach -t ok