#!/bin/bash
# Clean test instance entries from summary.csv and re-run all solvers in test mode

set -e
cd /home/lucifong/P3SAML3P

VENV=/home/lucifong/P3SAML3P/.venv/bin/python3

echo "=== Cleaning test instance entries from summary.csv files ==="
for solver in Atmostk CPLEX_ILP CPLEX_msls Incremental IncrementalSM IncrementalSM_E IncrementalSM_E_Shorten Incremental_E Incremental_E_Shorten Inheritant Staircase13 base maxsat; do
    f="Output/$solver/summary.csv"
    if [ -f "$f" ]; then
        # Keep header + non-test rows (rows NOT starting with test instance names)
        tmpfile=$(mktemp)
        head -1 "$f" > "$tmpfile"
        grep -v -E "^(MERTENS|MANSOOR|MITCHELL|BUXEY|SAWYER|GUNTHER|HESKIA)," "$f" >> "$tmpfile" 2>/dev/null || true
        cp "$tmpfile" "$f"
        rm -f "$tmpfile"
        echo "  Cleaned: $solver/summary.csv"
    else
        echo "  No summary.csv for: $solver"
    fi
done

echo ""
echo "=== Starting all solvers in test mode via run_launcher ==="
$VENV run_launcher.py --test \
    --scripts \
        Atmostk_run \
        CPLEX_ILP_run \
        CPLEX_msls_run \
        IncrementalSM_E_Shorten_run \
        IncrementalSM_E_run \
        IncrementalSM_run \
        Incremental_E_Shorten_run \
        Incremental_E_run \
        Incremental_run \
        Inheritant_run \
        Staircase_run \
        base_run \
        maxsat_run \
    2>&1

echo ""
echo "=== All solvers completed ==="
