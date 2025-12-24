import argparse
import csv
import math
import os
from collections import defaultdict
from statistics import mean
from pathlib import Path

# Default to the new consolidated Output/{solver} layout; still configurable via OUTPUT_ROOT.
DEFAULT_OUTPUT_ROOT = Path(os.environ.get("OUTPUT_ROOT", "Output/Staircase13"))


def find_summary_dirs():
    """
    Return output directories that contain a summary.csv.
    Prefer the new Output/{solver} layout, but fall back to legacy Output_*.
    """
    dirs = []
    output_root = Path("Output")
    if output_root.exists():
        for entry in output_root.iterdir():
            if entry.is_dir() and (entry / "summary.csv").exists():
                dirs.append(entry)
    if not dirs:
        # Legacy layout support: Output_* at repo root
        for entry in Path(".").iterdir():
            if entry.is_dir() and entry.name.startswith("Output_") and (entry / "summary.csv").exists():
                dirs.append(entry)
    return sorted(dirs)


def prompt_choose(options, label):
    """Prompt user to choose from options; default is 1."""
    print(f"Detected {label}:")
    for idx, opt in enumerate(options, start=1):
        print(f"[{idx}] {opt}")
    choice = input(f"Select {label} [1-{len(options)}] (default 1): ").strip()
    if not choice:
        return options[0]
    try:
        idx = int(choice)
    except ValueError:
        raise SystemExit("Invalid selection.")
    if idx < 1 or idx > len(options):
        raise SystemExit("Selection out of range.")
    return options[idx - 1]


def load_rows(csv_path: Path):
    with csv_path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def compute_best_lbs(rows):
    """
    Compute best lower bound for each (r_max, R_max) using neighbors:
    LB(r, R) = min( peak(r, R), LB(r-1, R), LB(r, R-1) ) when available.
    Returns a dict keyed by (r, R) -> lb value or None.
    """
    # Minimum peak per (r, R)
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
            if candidates:
                lbs[(r, R)] = min(candidates)
            else:
                lbs[(r, R)] = None
    return lbs


def calc_stats(rows):
    total = len(rows)
    if total == 0:
        return None
    runtimes = [float(r["runtime_sec"]) for r in rows]
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
        "cpu": mean(runtimes),
        "feas_pct": 100.0 * feas / total,
        "opt_pct": 100.0 * opt / total,
    }


def build_stats(rows):
    # Key by full instance signature to distinguish variants (e.g., same name, different m/c)
    by_instance = defaultdict(lambda: defaultdict(list))
    meta = {}
    for r in rows:
        key = (r["name"], int(r["n"]), int(r["m"]), int(r["c"]))
        rmax = int(r["r_max"])
        meta[key] = key[1:]  # (n, m, c)
        by_instance[key][rmax].append(r)

    stats = defaultdict(dict)
    for inst_key, bucket in by_instance.items():
        # compute best LB per (r, R) for this instance
        all_rows_inst = [r for rows_rmax in bucket.values() for r in rows_rmax]
        lb_grid = compute_best_lbs(all_rows_inst)
        # attach best_lb to rows
        for r in all_rows_inst:
            r["best_lb"] = lb_grid.get((int(r["r_max"]), int(r["R_max"])))
        for rmax, rows_rmax in bucket.items():
            stats[inst_key][rmax] = calc_stats(rows_rmax)
        stats[inst_key]["total"] = calc_stats(all_rows_inst)

    avg_row = {}
    for key in [1, 2, 3, "total"]:
        cpus, feas_vals, opt_vals, gaps = [], [], [], []
        for inst_key in stats:
            if key not in stats[inst_key]:
                continue
            s = stats[inst_key][key]
            if s is None:
                continue
            cpus.append(s["cpu"])
            feas_vals.append(s["feas_pct"])
            opt_vals.append(s["opt_pct"])
            if s["gap"] is not None:
                gaps.append(s["gap"])
        if cpus:
            avg_row[key] = {
                "gap": mean(gaps) if gaps else None,
                "cpu": mean(cpus),
                "feas_pct": mean(feas_vals),
                "opt_pct": mean(opt_vals),
            }
    return meta, stats, avg_row


def render_html(meta, stats, avg_row):
    style = """
<style>
:root {
    --bg: #f8fafc;
    --panel: #ffffff;
    --card: #ffffff;
    --border: #e2e8f0;
    --accent: #0ea5e9;
    --accent-2: #6366f1;
    --text: #0f172a;
    --muted: #475569;
    --block1: rgba(14, 165, 233, 0.10);
    --block2: rgba(99, 102, 241, 0.10);
    --block3: rgba(16, 185, 129, 0.12);
    --block4: rgba(248, 180, 0, 0.12);
}
body {
    margin: 0;
    padding: 24px;
    background: var(--bg);
    color: var(--text);
    font-family: "Inter", "Segoe UI", sans-serif;
}
.card {
    background: var(--card);
    border: 1px solid var(--border);
    border-radius: 14px;
    box-shadow: 0 12px 35px rgba(15, 23, 42, 0.12);
    padding: 18px 18px 6px 18px;
}
h3 {
    margin: 0 0 6px 0;
    letter-spacing: 0.4px;
    font-weight: 700;
}
p.desc {
    margin: 0 0 14px 0;
    color: var(--muted);
    font-size: 14px;
}
.table-wrap {
    overflow: auto;
    border: 1px solid var(--border);
    border-radius: 12px;
}
table {
    border-collapse: collapse;
    width: 100%;
    min-width: 960px;
    font-size: 13px;
    color: var(--text);
    background: var(--card);
}
th, td {
    padding: 10px 12px;
    text-align: right;
    border-bottom: 1px solid var(--border);
}
th {
    background: linear-gradient(135deg, rgba(14,165,233,0.16), rgba(99,102,241,0.12));
    color: #0f172a;
    font-weight: 700;
    position: sticky;
    top: 0;
    z-index: 1;
}
td.label {
    text-align: left;
    font-weight: 700;
    color: #0f172a;
}
tfoot td {
    font-weight: 800;
    background: rgba(14,165,233,0.10);
}
tbody tr:nth-child(odd) {
    background: rgba(15, 23, 42, 0.02);
}
tbody tr:hover {
    background: rgba(14,165,233,0.12);
}
.block-1 { background: var(--block1); border-right: 2px solid var(--border); }
.block-2 { background: var(--block2); border-right: 2px solid var(--border); }
.block-3 { background: var(--block3); border-right: 2px solid var(--border); }
.block-4 { background: var(--block4); }
.stub { background: rgba(15, 23, 42, 0.04); border-right: 2px solid var(--border); }
.pill {
    display: inline-block;
    padding: 2px 8px;
    border-radius: 999px;
    border: 1px solid rgba(15,23,42,0.08);
    background: rgba(14,165,233,0.10);
    font-weight: 700;
    font-size: 12px;
}
</style>
"""
    html = []
    html.append("<html><head>")
    html.append(style)
    html.append("</head><body>")
    html.append('<div class="card">')
    html.append("<h3>Summary statistics from summary.csv</h3>")
    html.append(
        '<p class="desc">Average runtime (cpu), feasible rate, and optimality rate per r_max. '
        "%LB is computed as (peak - best LB) / best LB, where best LB at (r_max, R_max) "
        "is the minimum of peak(r_max, R_max), LB(r_max-1, R_max), and LB(r_max, R_max-1) "
        "recursively.</p>"
    )
    html.append('<div class="table-wrap">')
    html.append("<table>")
    # multi-row header
    html.append(
        "<thead>"
        "<tr>"
        "<th rowspan=\"2\" class=\"stub\">instance</th>"
        "<th rowspan=\"2\" class=\"stub\">n</th>"
        "<th rowspan=\"2\" class=\"stub\">m</th>"
        "<th rowspan=\"2\" class=\"stub\">c</th>"
        "<th colspan=\"4\" class=\"block-1\">r_max = 1</th>"
        "<th colspan=\"4\" class=\"block-2\">r_max = 2</th>"
        "<th colspan=\"4\" class=\"block-3\">r_max = 3</th>"
        "<th colspan=\"4\" class=\"block-4\">Total</th>"
        "</tr>"
        "<tr>"
        "<th class=\"block-1\">%LB</th><th class=\"block-1\">cpu</th><th class=\"block-1\">feas(%)</th><th class=\"block-1\">opt(%)</th>"
        "<th class=\"block-2\">%LB</th><th class=\"block-2\">cpu</th><th class=\"block-2\">feas(%)</th><th class=\"block-2\">opt(%)</th>"
        "<th class=\"block-3\">%LB</th><th class=\"block-3\">cpu</th><th class=\"block-3\">feas(%)</th><th class=\"block-3\">opt(%)</th>"
        "<th class=\"block-4\">%LB</th><th class=\"block-4\">cpu</th><th class=\"block-4\">feas(%)</th><th class=\"block-4\">opt(%)</th>"
        "</tr>"
        "</thead>"
    )
    html.append("<tbody>")

    def fmt_gap(val):
        if val is None or (isinstance(val, float) and math.isnan(val)):
            return "n/a"
        return f"{val:.2f}%"

    def fmt_num(val):
        return "n/a" if val is None else f"{val:.2f}"

    def cell_block(s, block_class: str):
        if s is None:
            return [f'<td class="{block_class}">n/a</td>'] * 4
        return [
            f'<td class="{block_class}">{fmt_gap(s["gap"])}</td>',
            f'<td class="{block_class}">{fmt_num(s["cpu"])}</td>',
            f'<td class="{block_class}">{fmt_num(s["feas_pct"])}</td>',
            f'<td class="{block_class}">{fmt_num(s["opt_pct"])}</td>',
        ]

    # Sort by name, then ascending c, then m, then n for stable grouping
    for inst_key in sorted(meta, key=lambda k: (k[0], k[3], k[2], k[1])):
        name, n, m, c = inst_key
        cells = [
            f'<td class="label">{name}</td>',
            f"<td>{n}</td>",
            f"<td>{m}</td>",
            f"<td>{c}</td>",
        ]
        for idx, key in enumerate([1, 2, 3, "total"], start=1):
            cells.extend(cell_block(stats[inst_key].get(key), f"block-{idx}"))
        html.append("<tr>" + "".join(cells) + "</tr>")
    html.append("</tbody>")

    # average row
    avg_cells = [
        '<td class="label">Average</td>',
        "<td>-</td>",
        "<td>-</td>",
        "<td>-</td>",
    ]
    for idx, key in enumerate([1, 2, 3, "total"], start=1):
        avg_cells.extend(cell_block(avg_row.get(key), f"block-{idx}"))
    html.append("<tfoot><tr>" + "".join(avg_cells) + "</tr></tfoot>")
    html.append("</table>")
    html.append("</div>")  # table-wrap
    html.append("</div>")  # card
    html.append("</body></html>")
    return "\n".join(html)


def main():
    parser = argparse.ArgumentParser(description="Build summary table from summary.csv")
    parser.add_argument(
        "--csv",
        type=Path,
        default=None,
        help="Path to summary.csv. If omitted, will prompt from detected Output/* (or legacy Output_*) directories.",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output HTML path. Defaults to <csv_dir>/summary_table.html when omitted.",
    )
    parser.add_argument(
        "--auto",
        action="store_true",
        help="Auto-detect Output/* (or legacy Output_*) directories with summary.csv and prompt for selection (default when --csv not given)",
    )
    args = parser.parse_args()

    if args.auto or args.csv is None:
        dirs = find_summary_dirs()
        if not dirs:
            # Fallback to default location if it exists
            fallback_csv = DEFAULT_OUTPUT_ROOT / "summary.csv"
            if fallback_csv.exists():
                args.csv = fallback_csv
                args.out = args.out or fallback_csv.parent / "summary_table.html"
                print(f"No Output/* or Output_* detected; using default {args.csv}")
            else:
                raise SystemExit("No Output/* or Output_* directories with summary.csv found, and default summary.csv missing.")
        else:
            selected = prompt_choose(dirs, "output directory")
            args.csv = selected / "summary.csv"
            args.out = args.out or selected / "summary_table.html"
            print(f"Using CSV: {args.csv}")
            print(f"Output HTML: {args.out}")

    if args.csv is None:
        args.csv = DEFAULT_OUTPUT_ROOT / "summary.csv"
    if args.out is None:
        args.out = args.csv.parent / "summary_table.html"

    rows = load_rows(args.csv)
    meta, stats, avg_row = build_stats(rows)
    html = render_html(meta, stats, avg_row)

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(html, encoding="utf-8")
    print(f"Wrote {args.out}")


if __name__ == "__main__":
    main()
