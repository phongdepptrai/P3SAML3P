"""
Interactive launcher to run one of the local *_run.py wrappers.
Mimics the prompt style from generate_table.py: numbered options with default=1.
"""
import argparse
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent
RUNNERS_DIR = ROOT / "runners"


def find_run_scripts():
    """Return *_run.py files from runners/ (fallback to cwd), sorted by name."""
    scripts = []
    seen = set()
    for directory in (RUNNERS_DIR, ROOT):
        if not directory.exists():
            continue
        for path in directory.glob("*_run.py"):
            resolved = path.resolve()
            if resolved in seen:
                continue
            seen.add(resolved)
            scripts.append(path)
    return sorted(scripts, key=lambda p: p.name)


def prompt_choose(options):
    """Prompt user to select a run script; default is the first entry."""
    print("Detected run scripts:")
    for idx, opt in enumerate(options, start=1):
        print(f"[{idx}] {opt.name}")
    choice = input(f"Select script [1-{len(options)}] (default 1): ").strip()
    if not choice:
        return options[0]
    try:
        idx = int(choice)
    except ValueError:
        raise SystemExit("Invalid selection.")
    if idx < 1 or idx > len(options):
        raise SystemExit("Selection out of range.")
    return options[idx - 1]


def main():
    parser = argparse.ArgumentParser(
        description="Choose and run a *_run.py wrapper. Extra args after '--' are passed through."
    )
    parser.add_argument(
        "--script",
        type=Path,
        help="Name or path of the *_run.py script to execute. If omitted, a menu is shown.",
    )
    parser.add_argument(
        "extra",
        nargs=argparse.REMAINDER,
        help="Arguments passed to the selected *_run.py (prefix with '--' to separate).",
    )
    args = parser.parse_args()

    run_scripts = find_run_scripts()
    if not run_scripts:
        raise SystemExit("No *_run.py files found in runners/ or current directory.")

    if args.script is None:
        target = prompt_choose(run_scripts)
    else:
        candidate = args.script
        if candidate.suffix == "":
            candidate = candidate.with_suffix(".py")
        if not candidate.name.endswith("_run.py"):
            raise SystemExit("Target script must end with '_run.py'.")

        if not candidate.is_absolute():
            candidate = RUNNERS_DIR / candidate.name
        if not candidate.exists():
            fallback = ROOT / args.script.name
            if fallback.exists():
                candidate = fallback
            else:
                raise SystemExit(f"Script not found: {candidate}")
        target = candidate.resolve()

    cmd = [sys.executable, str(target)] + args.extra
    print(f"Executing: {' '.join(cmd)}")
    result = subprocess.run(cmd)
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
