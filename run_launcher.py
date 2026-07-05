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
        description="Choose and run a *_run.py wrapper."
    )
    parser.add_argument(
        "--script",
        type=Path,
        help="Name or path of the *_run.py script to execute. If omitted, a menu is shown.",
    )
    parser.add_argument(
        "--test",
        action="store_true",
        help="Run in test mode (appends --test)",
    )
    parser.add_argument(
        "--html",
        action="store_true",
        help="Generate HTML schedules (appends --html)",
    )
    args, unknown = parser.parse_known_args()

    run_scripts = find_run_scripts()
    if not run_scripts:
        raise SystemExit("No *_run.py files found in runners/ or current directory.")

    cli_test = "--test" in sys.argv
    cli_html = "--html" in sys.argv or "--write-html" in sys.argv

    test_mode = args.test
    html_mode = args.html

    if args.script is None:
        target = prompt_choose(run_scripts)
        # Prompt for options interactively if not passed via CLI
        if not cli_test:
            test_mode = input("Run in test mode (--test)? [y/N]: ").strip().lower() in ('y', 'yes')
        if not cli_html:
            html_mode = input("Generate HTML schedules (--html)? [y/N]: ").strip().lower() in ('y', 'yes')
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

    extra_args = []
    if test_mode:
        extra_args.append("--test")
    if html_mode:
        extra_args.append("--html")

    passed_args = [arg for arg in unknown if arg != "--"] + extra_args

    cmd = [sys.executable, str(target)] + passed_args
    print(f"Executing: {' '.join(cmd)}")
    result = subprocess.run(cmd)
    sys.exit(result.returncode)


if __name__ == "__main__":
    main()
