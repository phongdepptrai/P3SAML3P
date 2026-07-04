"""
compare_solvers.py
==================
Compare summary.csv files from multiple Output/<solver>/ directories.

Usage examples:
  # Interactive prompt (choose ≥2 solvers)
  python compare_solvers.py

  # Explicit paths
  python compare_solvers.py --csvs Output/Incremental/summary.csv Output/IncrementalSM/summary.csv

  # Explicit paths + custom output file
  python compare_solvers.py --csvs Output/Incremental/summary.csv Output/IncrementalSM/summary.csv --out comparison.html
"""

import argparse
import csv
import math
import os
from collections import defaultdict
from statistics import mean
from pathlib import Path


# ---------------------------------------------------------------------------
# Discovery helpers
# ---------------------------------------------------------------------------

def find_summary_dirs():
    """Return all Output/<solver> directories that contain a summary.csv."""
    dirs = []
    output_root = Path("Output")
    if output_root.exists():
        for entry in sorted(output_root.iterdir()):
            if entry.is_dir() and (entry / "summary.csv").exists():
                dirs.append(entry)
    if not dirs:
        # Legacy layout: Output_* at repo root
        for entry in sorted(Path(".").iterdir()):
            if entry.is_dir() and entry.name.startswith("Output_") and (entry / "summary.csv").exists():
                dirs.append(entry)
    return dirs


def prompt_multi_choose(options, label):
    """Prompt user to choose >=2 options (comma-separated indices, or 'all')."""
    print(f"\nDetected {label}:")
    for idx, opt in enumerate(options, start=1):
        print(f"  [{idx}] {opt}")
    raw = input(f"\nSelect >=2 {label} (comma-separated, e.g. 1,3 - or 'all'): ").strip()
    if raw.lower() == "all":
        return list(options)
    try:
        indices = [int(x) for x in raw.split(",")]
    except ValueError:
        raise SystemExit("Invalid selection - expected comma-separated numbers.")
    chosen = []
    for i in indices:
        if i < 1 or i > len(options):
            raise SystemExit(f"Index {i} out of range.")
        chosen.append(options[i - 1])
    if len(chosen) < 2:
        raise SystemExit("Please select at least 2 solvers to compare.")
    return chosen


# ---------------------------------------------------------------------------
# CSV loading & stats
# ---------------------------------------------------------------------------

def load_rows(csv_path: Path):
    with csv_path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def compute_best_lbs(rows):
    """
    Compute best lower bound for each (r_max, R_max) using neighbors:
    LB(r, R) = min( peak(r, R), LB(r-1, R), LB(r, R-1) ) when available.
    """
    peaks = {}
    for r in rows:
        rm = int(r["r_max"])
        RM = int(r["R_max"])
        peak_val = float(r["peak"])
        peaks[(rm, RM)] = min(peaks.get((rm, RM), peak_val), peak_val)

    lbs = {}
    r_vals = sorted({k[0] for k in peaks})
    for r in r_vals:
        R_vals = sorted({k[1] for k in peaks if k[0] == r})
        for R in R_vals:
            candidates = []
            if (r, R) in peaks:
                candidates.append(peaks[(r, R)])
            if (r - 1, R) in lbs:
                candidates.append(lbs[(r - 1, R)])
            if (r, R - 1) in lbs:
                candidates.append(lbs[(r, R - 1)])
            lbs[(r, R)] = min(candidates) if candidates else None
    return lbs


def calc_stats(rows):
    """Return dict with gap, cpu, feas_pct, opt_pct - or None if no rows."""
    total = len(rows)
    if total == 0:
        return None
    opt_runtimes = [float(r["runtime_sec"]) for r in rows if r["status"] == "OPTIMAL"]
    feas = sum(r["status"] in {"FEASIBLE", "INTERMEDIATE", "OPTIMAL"} for r in rows)
    opt = sum(r["status"] == "OPTIMAL" for r in rows)
    gap_vals = []
    for r in rows:
        lb_value = r.get("best_lb")
        if lb_value is None or lb_value <= 0:
            continue
        peak = float(r["peak"])
        gap_vals.append((peak - lb_value) / lb_value * 100.0)
    gap_avg = mean(gap_vals) if gap_vals else None
    return {
        "gap": gap_avg,
        "cpu": mean(opt_runtimes) if opt_runtimes else None,
        "feas_pct": 100.0 * feas / total,
        "opt_pct": 100.0 * opt / total,
    }


def build_stats(rows):
    """Build per-instance, per-r_max stats dict. Preserves first-seen order."""
    by_instance = defaultdict(lambda: defaultdict(list))
    meta = {}          # keeps insertion order (Python 3.7+)
    for r in rows:
        key = (r["name"], int(r["n"]), int(r["m"]), int(r["c"]))
        if key not in meta:
            meta[key] = key[1:]  # (n, m, c) – record only on first encounter
        by_instance[key][int(r["r_max"])].append(r)

    stats = defaultdict(dict)
    for inst_key, bucket in by_instance.items():
        all_rows_inst = [r for rrows in bucket.values() for r in rrows]
        lb_grid = compute_best_lbs(all_rows_inst)
        for r in all_rows_inst:
            r["best_lb"] = lb_grid.get((int(r["r_max"]), int(r["R_max"])))
        for rmax, rows_rmax in bucket.items():
            stats[inst_key][rmax] = calc_stats(rows_rmax)
        stats[inst_key]["total"] = calc_stats(all_rows_inst)

    # Global averages
    avg_row = {}
    for key in [1, 2, 3, "total"]:
        cpus, feas_vals, opt_vals, gaps = [], [], [], []
        has_stats = False
        for inst_key in stats:
            if key not in stats[inst_key]:
                continue
            s = stats[inst_key][key]
            if s is None:
                continue
            has_stats = True
            if s["cpu"] is not None:
                cpus.append(s["cpu"])
            feas_vals.append(s["feas_pct"])
            opt_vals.append(s["opt_pct"])
            if s["gap"] is not None:
                gaps.append(s["gap"])
        if has_stats:
            avg_row[key] = {
                "gap": mean(gaps) if gaps else None,
                "cpu": mean(cpus) if cpus else None,
                "feas_pct": mean(feas_vals),
                "opt_pct": mean(opt_vals),
            }
    return meta, stats, avg_row


# ---------------------------------------------------------------------------
# Delta helpers
# ---------------------------------------------------------------------------

def delta(val_a, val_b):
    """Return (b - a), or None if either is None."""
    if val_a is None or val_b is None:
        return None
    return val_b - val_a


def fmt_delta(val, higher_is_better=True):
    """Format a numeric delta with +/- prefix and colour class."""
    if val is None:
        return "<span class='nd'>n/d</span>"
    sign = "+" if val > 0 else ""
    text = f"{sign}{val:.2f}"
    if abs(val) < 1e-9:
        cls = "dz"
    elif val > 0:
        cls = "dpos" if higher_is_better else "dneg"
    else:
        cls = "dneg" if higher_is_better else "dpos"
    return f"<span class='{cls}'>{text}</span>"


# ---------------------------------------------------------------------------
# HTML rendering
# ---------------------------------------------------------------------------

STYLE = """
<style>
@import url('https://fonts.googleapis.com/css2?family=Inter:wght@400;500;600;700;800&display=swap');
:root {
    --bg: #0b0c10;
    --panel: #11141a;
    --card: #171b26;
    --border: #384259;
    --text: #e2e8f0;
    --muted: #718096;
    --accent: #38bdf8;
    --accent2: #818cf8;
    --green: #4ade80;
    --red: #f87171;
    --yellow: #fbbf24;
    --block1: rgba(56, 189, 248, 0.05);
    --block2: rgba(129, 140, 248, 0.05);
    --block3: rgba(74, 222, 128, 0.05);
    --block4: rgba(251, 191, 36, 0.05);
    --block1b: rgba(56, 189, 248, 0.12);
    --block2b: rgba(129, 140, 248, 0.12);
    --block3b: rgba(74, 222, 128, 0.12);
    --block4b: rgba(251, 191, 36, 0.12);
}
*, *::before, *::after { box-sizing: border-box; }
body {
    margin: 0;
    padding: 32px 40px 60px;
    background: var(--bg);
    color: var(--text);
    font-family: 'Inter', 'Segoe UI', sans-serif;
    font-size: 13px;
    line-height: 1.6;
}
.header-container {
    display: flex;
    flex-direction: column;
    margin-bottom: 24px;
}
h1 {
    margin: 0 0 6px;
    font-size: 26px;
    font-weight: 800;
    background: linear-gradient(90deg, var(--accent), var(--accent2));
    -webkit-background-clip: text;
    -webkit-text-fill-color: transparent;
    background-clip: text;
}
.subtitle {
    color: var(--muted);
    font-size: 13px;
    margin: 0 0 20px;
}
.badge {
    display: inline-flex;
    align-items: center;
    gap: 6px;
    padding: 4px 12px;
    border-radius: 999px;
    font-size: 11px;
    font-weight: 700;
    border: 1px solid;
    margin-right: 8px;
    transition: transform 0.2s ease;
}
.badge:hover {
    transform: translateY(-1px);
}
.solver-legend {
    display: flex;
    flex-wrap: wrap;
    gap: 8px;
    margin-bottom: 24px;
}

/* Tabs */
.tabs-container {
    display: flex;
    gap: 6px;
    margin-bottom: 20px;
    background: var(--panel);
    padding: 4px;
    border-radius: 10px;
    border: 1px solid var(--border);
    width: fit-content;
}
.tab-btn {
    background: transparent;
    border: none;
    color: var(--muted);
    padding: 8px 18px;
    border-radius: 7px;
    font-size: 12px;
    font-weight: 600;
    cursor: pointer;
    transition: all 0.2s ease;
}
.tab-btn:hover {
    color: var(--text);
    background: rgba(255, 255, 255, 0.03);
}
.tab-btn.active {
    color: #ffffff;
    background: var(--accent);
    box-shadow: 0 4px 12px rgba(56, 189, 248, 0.25);
}

.card {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 16px;
    box-shadow: 0 10px 40px rgba(0,0,0,0.5);
    padding: 24px;
    margin-bottom: 32px;
}
.card-title {
    font-size: 15px;
    font-weight: 700;
    color: var(--text);
    margin: 0 0 16px;
    letter-spacing: 0.3px;
    display: flex;
    align-items: center;
    gap: 8px;
}
.table-wrap {
    overflow-x: auto;
    border-radius: 12px;
    border: 1px solid var(--border);
    background: var(--panel);
}
table {
    border-collapse: collapse;
    width: 100%;
    min-width: 1000px;
    font-size: 12px;
}
th, td {
    padding: 10px 14px;
    text-align: right;
    border-bottom: 1px solid var(--border);
    border-right: 1px solid var(--border);
    white-space: nowrap;
}
th:first-child, td:first-child {
    border-left: 1px solid var(--border);
}
td {
    font-variant-numeric: tabular-nums;
    color: #a0aec0;
}
th {
    color: var(--muted);
    font-weight: 700;
    font-size: 11px;
    text-transform: uppercase;
    letter-spacing: 0.5px;
    position: sticky;
    top: 0;
    z-index: 2;
    background: var(--panel);
}
thead tr:first-child th {
    border-bottom: 2px solid var(--border);
    font-size: 12px;
    text-transform: none;
    font-weight: 800;
    color: var(--text);
}
td.label {
    text-align: left;
    font-weight: 700;
    color: #ffffff;
}
td.stub, th.stub {
    text-align: center;
}
td.label.stub {
    text-align: left;
}
tfoot td {
    font-weight: 800;
    background: rgba(251, 191, 36, 0.06) !important;
    border-top: 2px solid var(--yellow) !important;
    color: var(--yellow) !important;
}
tfoot td * {
    color: var(--yellow) !important;
    text-shadow: none !important;
}
tbody tr:hover td { background: rgba(255, 255, 255, 0.02) !important; }

/* Block columns */
.stub  { background: var(--panel) !important; border-right: 2px solid var(--border); }
.b1    { background: var(--block1); }
.b1h   { background: var(--block1b); border-right: 2px solid var(--border); }
.b2    { background: var(--block2); }
.b2h   { background: var(--block2b); border-right: 2px solid var(--border); }
.b3    { background: var(--block3); }
.b3h   { background: var(--block3b); border-right: 2px solid var(--border); }
.b4    { background: var(--block4); }
.b4h   { background: var(--block4b); }

/* Winners highlight */
td.winner {
    background: rgba(74, 222, 128, 0.08) !important;
    color: var(--green) !important;
    font-weight: 700;
    box-shadow: inset 0 0 0 1px rgba(74, 222, 128, 0.15);
}

/* Delta columns visual highlighting */
.delta-cell {
    background-color: rgba(255, 255, 255, 0.035) !important;
}
th.delta-cell {
    background-color: rgba(255, 255, 255, 0.06) !important;
}
tbody tr:hover td.delta-cell {
    background-color: rgba(255, 255, 255, 0.08) !important;
}

/* Brighter & glowing delta values */
.dpos { color: #55efc4; font-weight: 800; text-shadow: 0 0 6px rgba(85, 239, 196, 0.15); }
.dneg { color: #ff7675; font-weight: 800; text-shadow: 0 0 6px rgba(255, 118, 117, 0.15); }
.dz   { color: #ffffff; font-weight: 700; }
.nd   { color: var(--muted); font-style: italic; opacity: 0.6; }

.dot { display: inline-block; width: 8px; height: 8px; border-radius: 50%; margin-right: 6px; }

/* Hide functionality via class toggles */
table.show-only-1 .block-2-cell,
table.show-only-1 .block-3-cell,
table.show-only-1 .block-4-cell {
    display: none !important;
}
table.show-only-2 .block-1-cell,
table.show-only-2 .block-3-cell,
table.show-only-2 .block-4-cell {
    display: none !important;
}
table.show-only-3 .block-1-cell,
table.show-only-3 .block-2-cell,
table.show-only-3 .block-4-cell {
    display: none !important;
}
table.show-only-4 .block-1-cell,
table.show-only-4 .block-2-cell,
table.show-only-4 .block-3-cell {
    display: none !important;
}

/* Scrollbars */
::-webkit-scrollbar { height: 7px; width: 7px; }
::-webkit-scrollbar-track { background: var(--panel); }
::-webkit-scrollbar-thumb { background: var(--border); border-radius: 4px; }
::-webkit-scrollbar-thumb:hover { background: var(--accent); }
</style>
"""

SOLVER_COLORS = [
    "#38bdf8",  # sky
    "#818cf8",  # indigo
    "#4ade80",  # emerald
    "#fbbf24",  # amber
    "#f472b6",  # pink
    "#a78bfa",  # violet
]


def _color(idx):
    return SOLVER_COLORS[idx % len(SOLVER_COLORS)]


def fmt_gap(val):
    if val is None or (isinstance(val, float) and math.isnan(val)):
        return "n/a"
    return f"{val:.2f}%"


def fmt_num(val):
    return "n/a" if val is None else f"{val:.2f}"


def _block_cls(block_idx, last_in_block):
    base = ["b1", "b2", "b3", "b4"][block_idx]
    return base + "h" if last_in_block else base


def get_winners(solver_stats):
    """
    Returns a dict mapping metric name -> set of solver indices that are the winners.
    Only highlights if there is a difference among solvers to reduce noise.
    """
    metrics = {
        "gap": False,       # lower is better
        "cpu": False,       # lower is better
        "feas_pct": True,   # higher is better
        "opt_pct": True,    # higher is better
    }
    winners = {m: set() for m in metrics}
    for m, higher_better in metrics.items():
        vals = []
        for idx, s in enumerate(solver_stats):
            if s is not None and s.get(m) is not None:
                vals.append((s[m], idx))
        if not vals:
            continue
        unique_vals = {v[0] for v in vals}
        if len(unique_vals) <= 1:
            # No highlight when all values are identical
            continue
        vals.sort(key=lambda x: x[0], reverse=higher_better)
        best_val = vals[0][0]
        for val, idx in vals:
            if abs(val - best_val) < 1e-9:
                winners[m].add(idx)
    return winners


def _solver_cells(s, block_idx, is_last_col, si, winners):
    bc = _block_cls(block_idx, False) + f" block-{block_idx+1}-cell"
    bc_end = _block_cls(block_idx, is_last_col) + f" block-{block_idx+1}-cell"
    
    if s is None:
        return (
            f'<td class="{bc}">n/a</td>'
            f'<td class="{bc}">n/a</td>'
            f'<td class="{bc}">n/a</td>'
            f'<td class="{bc_end}">n/a</td>'
        )
        
    def _cell(metric, val, fmt_fn, cls):
        is_winner = si in winners.get(metric, set())
        win_cls = " winner" if is_winner else ""
        return f'<td class="{cls}{win_cls}">{fmt_fn(val)}</td>'
        
    return (
        _cell("gap", s["gap"], fmt_gap, bc) +
        _cell("cpu", s["cpu"], fmt_num, bc) +
        _cell("feas_pct", s["feas_pct"], fmt_num, bc) +
        _cell("opt_pct", s["opt_pct"], fmt_num, bc_end)
    )


def _delta_cells(sA, sB, block_idx, is_last_col):
    bc = _block_cls(block_idx, False) + f" block-{block_idx+1}-cell delta-cell"
    bc_end = _block_cls(block_idx, is_last_col) + f" block-{block_idx+1}-cell delta-cell"
    metrics = [
        ("gap", False, bc),
        ("cpu", False, bc),
        ("feas_pct", True, bc),
        ("opt_pct", True, bc_end),
    ]
    out = ""
    for metric, higher_better, cls in metrics:
        vA = sA[metric] if sA else None
        vB = sB[metric] if sB else None
        d = delta(vA, vB)
        out += f'<td class="{cls}">{fmt_delta(d, higher_is_better=higher_better)}</td>'
    return out


def render_html(solver_names, all_meta, all_stats, all_avg_rows):
    n = len(solver_names)
    colors = [_color(i) for i in range(n)]
    r_max_keys = [1, 2, 3, "total"]
    block_labels = ["r_max = 1", "r_max = 2", "r_max = 3", "Total Summary"]
    metrics_labels = ["%LB", "cpu", "feas%", "opt%"]

    # Union of all instance keys – preserve first-seen order across all solvers
    seen = {}
    for meta in all_meta:
        for k in meta:          # meta is an ordered dict
            if k not in seen:
                seen[k] = None
    all_inst_keys = list(seen.keys())

    # Columns per block: n solvers * 4 metrics + (n-1) delta groups * 4 metrics
    cols_per_block = n * 4 + (n - 1) * 4  # = (2n-1)*4

    html = [
        "<html><head><meta charset='utf-8'>",
        "<title>Solver Comparison</title>",
        STYLE,
        "</head><body>",
        "<div class='header-container'>",
        "<h1>Solver Comparison</h1>",
        f'<p class="subtitle">Comparing {n} solvers '
        "&nbsp;·&nbsp; metrics: %LB (lower is better), cpu (s), feas(%), opt(%) "
        "&nbsp;·&nbsp; \u0394 columns = second solver \u2212 first</p>",
        "</div>",
    ]

    # Legend
    html.append('<div class="solver-legend">')
    for i, sname in enumerate(solver_names):
        c = colors[i]
        html.append(
            f'<span class="badge" style="color:{c};border-color:{c}33;background:{c}18;">'
            f'<span class="dot" style="background:{c}"></span>{sname}</span>'
        )
    html.append("</div>")

    # Tab selectors
    html.append('<div class="tabs-container">')
    html.append('<button class="tab-btn active" onclick="switchTab(\'all\')">Show All Blocks</button>')
    html.append('<button class="tab-btn" onclick="switchTab(1)">r_max = 1</button>')
    html.append('<button class="tab-btn" onclick="switchTab(2)">r_max = 2</button>')
    html.append('<button class="tab-btn" onclick="switchTab(3)">r_max = 3</button>')
    html.append('<button class="tab-btn" onclick="switchTab(4)">Total Summary</button>')
    html.append('</div>')

    # Card + table
    html.append('<div class="card">')
    html.append('<div class="card-title">📊 Instance-level Performance &amp; Delta</div>')
    html.append('<div class="table-wrap"><table><thead>')

    # Header row 1: stub + block spans
    html.append("<tr>")
    html.append('<th rowspan="3" colspan="4" class="stub" style="text-align:left">Instance</th>')
    for bidx, blabel in enumerate(block_labels):
        bc = _block_cls(bidx, True) + f" block-{bidx+1}-cell"
        html.append(f'<th colspan="{cols_per_block}" class="{bc}" style="text-align:center">{blabel}</th>')
    html.append("</tr>")

    # Header row 2: solver names + delta labels per block
    html.append("<tr>")
    for bidx in range(4):
        for si, sname in enumerate(solver_names):
            is_last_group = (si == n - 1)
            bc = _block_cls(bidx, is_last_group) + f" block-{bidx+1}-cell"
            html.append(f'<th colspan="4" class="{_block_cls(bidx, False)} block-{bidx+1}-cell" style="color:{colors[si]}">{sname}</th>')
            if not is_last_group:
                next_name = solver_names[si + 1]
                is_last_delta = (si == n - 2)
                bc_d = _block_cls(bidx, is_last_delta) + f" block-{bidx+1}-cell delta-cell"
                html.append(f'<th colspan="4" class="{bc_d}" style="color:var(--muted)">\u0394({next_name}\u2212{sname})</th>')
    html.append("</tr>")

    # Header row 3: metric names
    html.append("<tr>")
    for bidx in range(4):
        for si in range(n):
            is_last_solver = (si == n - 1)
            for mi, ml in enumerate(metrics_labels):
                last = is_last_solver and (mi == 3)
                bc = _block_cls(bidx, last) + f" block-{bidx+1}-cell"
                html.append(f'<th class="{bc}">{ml}</th>')
            if not is_last_solver:
                is_last_delta = (si == n - 2)
                for mi, ml in enumerate(metrics_labels):
                    last = is_last_delta and (mi == 3)
                    bc = _block_cls(bidx, last) + f" block-{bidx+1}-cell delta-cell"
                    html.append(f'<th class="{bc}">\u0394{ml}</th>')
    html.append("</tr></thead><tbody>")

    # Data rows
    for inst_key in all_inst_keys:
        name, nv, m, c = inst_key
        html.append("<tr>")
        html.append(f'<td class="label stub">{name}</td>')
        html.append(f'<td class="stub" style="color:var(--muted)">{nv}</td>')
        html.append(f'<td class="stub" style="color:var(--muted)">{m}</td>')
        html.append(f'<td class="stub" style="color:var(--muted)">{c}</td>')
        for bidx, rk in enumerate(r_max_keys):
            solver_stats = [all_stats[si].get(inst_key, {}).get(rk) for si in range(n)]
            winners = get_winners(solver_stats)
            for si, s in enumerate(solver_stats):
                is_last_solver = (si == n - 1)
                html.append(_solver_cells(s, bidx, is_last_solver, si, winners))
                if not is_last_solver:
                    is_last_delta = (si == n - 2)
                    html.append(_delta_cells(s, solver_stats[si + 1], bidx, is_last_delta))
        html.append("</tr>")

    # Averages / Footer
    html.append("</tbody><tfoot><tr>")
    html.append('<td class="label stub" colspan="4">Average</td>')
    for bidx, rk in enumerate(r_max_keys):
        avg_stats = [ar.get(rk) for ar in all_avg_rows]
        winners = get_winners(avg_stats)
        for si, s in enumerate(avg_stats):
            is_last_solver = (si == n - 1)
            html.append(_solver_cells(s, bidx, is_last_solver, si, winners))
            if not is_last_solver:
                is_last_delta = (si == n - 2)
                html.append(_delta_cells(s, avg_stats[si + 1], bidx, is_last_delta))
    html.append("</tr></tfoot></table></div></div>")

    # Footer description & JavaScript
    html.append(
        '<p style="color:var(--muted);font-size:11px;margin-top:16px;">'
        "Generated by compare_solvers.py &nbsp;·&nbsp; "
        "\u0394 = next solver \u2212 current &nbsp;·&nbsp; "
        "%LB = (peak \u2212 best_LB) / best_LB \u00d7 100</p>"
    )
    
    html.append("""
<script>
function switchTab(blockId) {
    // Update active tab button style
    const buttons = document.querySelectorAll('.tab-btn');
    buttons.forEach((btn, index) => {
        btn.classList.remove('active');
        if (blockId === 'all' && index === 0) {
            btn.classList.add('active');
        } else if (blockId !== 'all' && index === blockId) {
            btn.classList.add('active');
        }
    });
    
    // Update table class to filter columns
    const table = document.querySelector('table');
    table.className = ''; // Reset classes
    if (blockId !== 'all') {
        table.classList.add('show-only-' + blockId);
    }
}
</script>
""")
    html.append("</body></html>")
    return "\n".join(html)


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    parser = argparse.ArgumentParser(
        description="Compare summary.csv files from multiple Output/<solver>/ directories."
    )
    parser.add_argument(
        "--csvs",
        nargs="+",
        type=Path,
        default=None,
        help="Paths to 2+ summary.csv files. If omitted, will auto-detect and prompt.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output HTML path. Default: Output/comparison_<A>_vs_<B>.html",
    )
    args = parser.parse_args()

    # Resolve CSV paths
    if args.csvs:
        csv_paths = args.csvs
        for p in csv_paths:
            if not p.exists():
                raise SystemExit(f"File not found: {p}")
    else:
        dirs = find_summary_dirs()
        if not dirs:
            raise SystemExit("No Output/* directories with summary.csv found.")
        chosen_dirs = prompt_multi_choose(dirs, "solver directories")
        csv_paths = [d / "summary.csv" for d in chosen_dirs]

    if len(csv_paths) < 2:
        raise SystemExit("Need at least 2 CSV files to compare.")

    # Derive solver names from parent directory names
    solver_names = [p.parent.name for p in csv_paths]

    # Load & build stats
    all_meta = []
    all_stats_list = []
    all_avg_rows = []
    for p, sname in zip(csv_paths, solver_names):
        print(f"  Loading {sname}: {p}")
        rows = load_rows(p)
        meta, stats, avg_row = build_stats(rows)
        all_meta.append(meta)
        all_stats_list.append(stats)
        all_avg_rows.append(avg_row)

    # Default output path
    if args.out is None:
        tag = "_vs_".join(solver_names)
        args.out = Path("Output") / f"comparison_{tag}.html"

    html = render_html(solver_names, all_meta, all_stats_list, all_avg_rows)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(html, encoding="utf-8")
    print(f"\nComparison written to: {args.out}")


if __name__ == "__main__":
    main()
