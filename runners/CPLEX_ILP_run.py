import subprocess
import sys
import shutil
import shlex
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Detect if we should run under WSL
use_wsl = False
if sys.platform != 'linux' and shutil.which("wsl"):
    use_wsl = True

if use_wsl:
    WSL_ROOT = "/home/lucifong/P3SAML3P"
    VENV_PY = f"{WSL_ROOT}/.venv/bin/python3"
    SCRIPT = f"{WSL_ROOT}/solvers/CPLEX_ILP.py"
    WINDOWS_OUTPUT = "/mnt/c/Users/admin/Documents/Python/P3SAML3P/Output/CPLEX_ILP"

    sync_cmd = f"rsync -a --exclude='.venv*' --exclude='Output/' /mnt/c/Users/admin/Documents/Python/P3SAML3P/ {WSL_ROOT}/"
    run_cmd = f"export OUTPUT_ROOT='{WINDOWS_OUTPUT}' && cd '{WSL_ROOT}' && '{VENV_PY}' '{SCRIPT}'"
    if len(sys.argv) > 1:
        args = " ".join(shlex.quote(arg) for arg in sys.argv[1:])
        run_cmd += f" {args}"

    bash_cmd = f"{sync_cmd} && {run_cmd}"
    wsl_command = ['wsl', 'bash', '-c', bash_cmd]
    print(f"Running in WSL: {bash_cmd}")
    result = subprocess.run(wsl_command)
    sys.exit(result.returncode)
else:
    SCRIPT = ROOT / "solvers" / "CPLEX_ILP.py"
    cmd = [sys.executable, str(SCRIPT)] + sys.argv[1:]
    print(f"Running natively: {' '.join(cmd)}")
    result = subprocess.run(cmd)
    sys.exit(result.returncode)
