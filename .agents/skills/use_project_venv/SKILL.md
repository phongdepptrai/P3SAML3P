---
name: use-project-venv
description: >
  Detect and use the correct Python virtual environment (.venv) when running
  Python scripts in P3SAML3P or SAML3P workspaces. Always call this skill
  before executing any python3 command, launching screen sessions, or running
  solver scripts in these projects.
---

# Use Project Virtual Environment

## Rule

**NEVER use bare `python3` or `python` when running scripts in P3SAML3P or SAML3P.**
Always resolve the project venv Python path first.

## Detection Order

Run the following to find the correct interpreter (in order of priority):

```bash
# 1. WSL home venv used by project runners (preferred for this workspace)
ls /home/lucifong/P3SAML3P/.venv/bin/python3

# 2. Project-local .venv
ls <PROJECT_ROOT>/.venv/bin/python3

# 3. Project-local venv (alternative name)
ls <PROJECT_ROOT>/venv/bin/python3

# 4. Windows-mounted WSL venv fallback
ls <PROJECT_ROOT>/.venv_wsl/bin/python3

# 5. Fall back to system python only if none found
which python3
```

## Known Venv Locations

| Project | Venv Python Path |
|---|---|
| P3SAML3P | `/home/lucifong/P3SAML3P/.venv/bin/python3` |
| P3SAML3P Windows-mounted fallback | `<PROJECT_ROOT>/.venv_wsl/bin/python3` *(may not have docplex/cplex)* |
| SAML3P | `/home/lucifong/SAML3P/.venv/bin/python3` *(verify if exists)* |

## How to Use in Commands

### Direct script execution
```bash
# WRONG
python3 solvers/Incremental.py

# CORRECT
/home/lucifong/P3SAML3P/.venv/bin/python3 solvers/Incremental.py
```

### Screen sessions
```bash
# WRONG
screen -S myscreen -dm bash -c "python3 solvers/Incremental.py"

# CORRECT
VENV=/home/lucifong/P3SAML3P/.venv/bin/python3
screen -S myscreen -dm bash -c "cd /home/lucifong/P3SAML3P && $VENV solvers/Incremental.py 2>&1 | tee logs/myscreen.log; exec bash"
```

### As a variable (reusable pattern)
```bash
VENV=$(find /home/lucifong/P3SAML3P/.venv/bin -name "python3" | head -1)
$VENV <script> <args>
```

## Verification

Always verify the venv has the required packages before running:
```bash
/home/lucifong/P3SAML3P/.venv/bin/python3 -c "import pysat; print('pysat OK')"
/home/lucifong/P3SAML3P/.venv/bin/python3 -c "import docplex, cplex; print(cplex.Cplex().get_version())"
```

If `ModuleNotFoundError` appears for `pysat`, `docplex`, `cplex`, or other packages, it means
the wrong Python was used — retry with the explicit venv path above.

## Notes

- The project uses `runlim` for timeout-wrapped subprocess calls; the venv path
  is passed directly to `runlim` as `argv[0]` — this is correct behavior.
- When the solver scripts call themselves via `subprocess.Popen`, they use
  `sys.executable` which correctly inherits the venv interpreter if launched
  with the venv Python.
