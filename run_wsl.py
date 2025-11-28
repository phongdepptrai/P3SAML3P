"""
Wrapper script to run test.py entirely in WSL
This avoids Windows Python dependency issues
"""
import subprocess
import sys

# Build command
bash_cmd = "cd /mnt/c/Users/admin/Documents/Python/P3SAML3P && .venv_wsl/bin/python test.py"

# Add any command line arguments
if len(sys.argv) > 1:
    args = " ".join(sys.argv[1:])
    bash_cmd += f" {args}"

# Run test.py in WSL with proper quoting
wsl_command = ['wsl', 'bash', '-c', bash_cmd]

# Execute in WSL
print(f"Running in WSL: {bash_cmd}")
result = subprocess.run(wsl_command)
sys.exit(result.returncode)
