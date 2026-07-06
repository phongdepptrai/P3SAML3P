"""
Interactive launcher to run one or more local *_run.py wrappers.
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


def parse_selection(choice, count):
    """Parse menu selections such as '1', '1,3,5', '2-4', or 'all'."""
    if not choice:
        return [0]
    lowered = choice.lower()
    if lowered in {"a", "all", "*"}:
        return list(range(count))

    selected = []
    seen = set()
    for part in choice.split(","):
        token = part.strip()
        if not token:
            continue
        if "-" in token:
            bounds = token.split("-", 1)
            if len(bounds) != 2 or not bounds[0].strip() or not bounds[1].strip():
                raise SystemExit("Invalid range selection.")
            try:
                start = int(bounds[0])
                end = int(bounds[1])
            except ValueError:
                raise SystemExit("Invalid range selection.")
            if start > end:
                raise SystemExit("Range start must be <= range end.")
            indices = range(start, end + 1)
        else:
            try:
                indices = [int(token)]
            except ValueError:
                raise SystemExit("Invalid selection.")

        for idx in indices:
            if idx < 1 or idx > count:
                raise SystemExit("Selection out of range.")
            zero_idx = idx - 1
            if zero_idx not in seen:
                seen.add(zero_idx)
                selected.append(zero_idx)

    if not selected:
        raise SystemExit("No scripts selected.")
    return selected


def prompt_choose(options):
    """Prompt user to select one or more run scripts; default is the first entry."""
    print("Detected run scripts:")
    for idx, opt in enumerate(options, start=1):
        print(f"[{idx}] {opt.name}")
    choice = input(
        f"Select script(s) [1-{len(options)}], e.g. 1,3,5 or 2-4 or all (default 1): "
    ).strip()
    return [options[idx] for idx in parse_selection(choice, len(options))]


def resolve_script(candidate):
    if candidate.suffix == "":
        candidate = candidate.with_suffix(".py")
    if not candidate.name.endswith("_run.py"):
        raise SystemExit("Target script must end with '_run.py'.")

    if not candidate.is_absolute():
        candidate = RUNNERS_DIR / candidate.name
    if not candidate.exists():
        fallback = ROOT / candidate.name
        if fallback.exists():
            candidate = fallback
        else:
            raise SystemExit(f"Script not found: {candidate}")
    return candidate.resolve()


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
        "--scripts",
        nargs="+",
        type=Path,
        help="Names or paths of multiple *_run.py scripts to execute sequentially.",
    )
    parser.add_argument(
        "--continue-on-error",
        action="store_true",
        help="Continue with the next selected script if one exits with a non-zero status.",
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

    if args.script is not None and args.scripts is not None:
        raise SystemExit("Use either --script or --scripts, not both.")

    if args.script is None and args.scripts is None:
        targets = prompt_choose(run_scripts)
        # Prompt for options interactively if not passed via CLI
        if not cli_test:
            test_mode = input("Run in test mode (--test)? [y/N]: ").strip().lower() in ('y', 'yes')
        if not cli_html:
            html_mode = input("Generate HTML schedules (--html)? [y/N]: ").strip().lower() in ('y', 'yes')
    elif args.scripts is not None:
        targets = [resolve_script(candidate) for candidate in args.scripts]
    else:
        targets = [resolve_script(args.script)]

    extra_args = []
    if test_mode:
        extra_args.append("--test")
    if html_mode:
        extra_args.append("--html")

    passed_args = [arg for arg in unknown if arg != "--"] + extra_args

    for target in targets:
        cmd = [sys.executable, str(target)] + passed_args
        print(f"\n===== START {target.name} =====")
        print(f"Executing: {' '.join(cmd)}")
        result = subprocess.run(cmd)
        print(f"===== END {target.name} exit={result.returncode} =====\n")
        if result.returncode != 0 and not args.continue_on_error:
            sys.exit(result.returncode)
    sys.exit(0)


if __name__ == "__main__":
    main()
