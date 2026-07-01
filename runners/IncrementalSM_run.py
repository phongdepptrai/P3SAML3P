import subprocess
import sys
import shutil
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

# Detect if we should run under WSL
use_wsl = False
if sys.platform != 'linux' and shutil.which("wsl"):
    use_wsl = True

if use_wsl:
    WSL_ROOT = "/mnt/c/Users/admin/Documents/Python/P3SAML3P"
    VENV_PY = f"{WSL_ROOT}/.venv_wsl/bin/python"
    SCRIPT = f"{WSL_ROOT}/solvers/IncrementalSM.py"
    bash_cmd = f"cd '{WSL_ROOT}' && '{VENV_PY}' '{SCRIPT}'"
    if len(sys.argv) > 1:
        args = " ".join(sys.argv[1:])
        bash_cmd += f" {args}"
    wsl_command = ['wsl', 'bash', '-c', bash_cmd]
    print(f"Running in WSL: {bash_cmd}")
    result = subprocess.run(wsl_command)
    sys.exit(result.returncode)
else:
    SCRIPT = ROOT / "solvers" / "IncrementalSM.py"
    cmd = [sys.executable, str(SCRIPT)] + sys.argv[1:]
    print(f"Running natively: {' '.join(cmd)}")
    result = subprocess.run(cmd)
    sys.exit(result.returncode)
