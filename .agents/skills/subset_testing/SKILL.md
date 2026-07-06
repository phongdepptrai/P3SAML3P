---
name: run-test-subset
description: How to quickly test solvers using a representative subset of problems instead of the full benchmark suite.
---

# Running a Test Subset of SAML3P Solvers

When developing, debugging, or verifying changes to SAML3P solvers, you often don't want to wait for the entire benchmark suite to run. You can use the `--test` flag to quickly execute a small, representative subset of instances (Easy, Medium, Hard).

## How to use

Run any solver script with the `--test` flag appended. Make sure you are using the project's virtual environment (`.venv`) so that dependencies like `pysat` are loaded correctly:

```bash
# Using the virtual environment directly
.venv/bin/python3 solvers/IncrementalSM.py --test

# OR, activate it first
source .venv/bin/activate
python3 solvers/Atmostk.py --test
```

## How it works

- The flag `--test` instructs the solver to use `test_data_set` instead of `data_set`.
- The `test_data_set` includes:
  - Easy: MERTENS (6, 6)
  - Medium: MANSOOR (4, 48), MITCHELL (8, 14)
  - Hard: BUXEY (14, 25), SAWYER (14, 25)
- The solver's background worker processes (spawned via `runlim`) are automatically passed the `--test` flag, ensuring they load the correct instance parameters for the test subset.

## Best Practices

- Always run a `--test` benchmark after making core changes to constraint formulations (e.g. `SM[i][j]`, staircases) to ensure they are satisfiable and computationally sound before launching full overnight benchmarks.
- Use `screen` if you still want to detach from the test run, though test runs typically finish in a few minutes.

## Orphaned Process Prevention (CRITICAL)

When you (the agent) run a test in the background, you **MUST NOT** leave it running indefinitely and forget about it. Furthermore, **DO NOT** use task cancellation (`manage_task kill`) or `killall runlim` to abort tests!
Standard task cancellation will leave `runlim` child processes **orphaned** to corrupt the output. Using `killall` is dangerous because it will kill the USER's background processes too!

**To safely do a quick dry-run without affecting the user's processes:**
Launch the test in a new process group using `setsid`, let it run, and then kill its specific process group (`-$PGID`). This guarantees the entire process tree (including `runlim` and its children) is cleanly wiped out, without touching the user's manual runs.

Use the `run_command` tool to run a one-liner like this:
```bash
# Example: Run for 30 seconds, then kill the entire process group cleanly
setsid .venv/bin/python3 solvers/IncrementalSM.py --test > test_dry_run.log 2>&1 & PGID=$!; sleep 30; kill -TERM -$PGID
```
After it completes, use `view_file` to read `test_dry_run.log` and verify the syntax/logic.
