"""
Wrapper script to run solvers/base.py entirely in WSL.
This avoids Windows Python dependency issues.
"""
import subprocess
import sys

# Use absolute paths and quote for safety
WSL_ROOT = "/mnt/c/Users/admin/Documents/Python/P3SAML3P"
VENV_PY = f"{WSL_ROOT}/.venv_wsl/bin/python"
SCRIPT = f"{WSL_ROOT}/solvers/base.py"

# Build command
bash_cmd = f"cd '{WSL_ROOT}' && '{VENV_PY}' '{SCRIPT}'"

# Add any command line arguments
if len(sys.argv) > 1:
    args = " ".join(sys.argv[1:])
    bash_cmd += f" {args}"

wsl_command = ['wsl', 'bash', '-c', bash_cmd]

# Execute in WSL
print(f"Running in WSL: {bash_cmd}")
result = subprocess.run(wsl_command)
sys.exit(result.returncode)
