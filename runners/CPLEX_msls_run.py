import shlex
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Detect if we should run under WSL.
use_wsl = False
if sys.platform != "linux" and shutil.which("wsl"):
    use_wsl = True

if use_wsl:
    WSL_ROOT = "/home/lucifong/P3SAML3P"
    VENV_PY = f"{WSL_ROOT}/.venv/bin/python3"
    SCRIPT = f"{WSL_ROOT}/solvers/CPLEX_msls.py"
    WINDOWS_OUTPUT = "/mnt/c/Users/admin/Documents/Python/P3SAML3P/Output/CPLEX_msls"

    sync_cmd = (
        "rsync -rt --delete "
        "--exclude='.venv*' --exclude='Output/' --exclude='.git/' "
        "--exclude='.codex/' --exclude='__pycache__/' "
        f"/mnt/c/Users/admin/Documents/Python/P3SAML3P/ {WSL_ROOT}/"
    )
    run_cmd = f"export OUTPUT_ROOT='{WINDOWS_OUTPUT}'; cd '{WSL_ROOT}'; '{VENV_PY}' '{SCRIPT}'"
    if len(sys.argv) > 1:
        args = " ".join(shlex.quote(arg) for arg in sys.argv[1:])
        run_cmd += f" {args}"

    print(f"Syncing project to WSL: {sync_cmd}", flush=True)
    sync_result = subprocess.run(["wsl", "bash", "-lc", sync_cmd])
    if sync_result.returncode != 0:
        sys.exit(sync_result.returncode)

    print(f"Running in WSL: {run_cmd}", flush=True)
    result = subprocess.run(["wsl", "bash", "-lc", run_cmd])
    sys.exit(result.returncode)
else:
    SCRIPT = ROOT / "solvers" / "CPLEX_msls.py"
    cmd = [sys.executable, str(SCRIPT)] + sys.argv[1:]
    print(f"Running natively: {' '.join(cmd)}", flush=True)
    result = subprocess.run(cmd)
    sys.exit(result.returncode)
