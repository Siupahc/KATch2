"""Plot the Topology Zoo campaigns. Run after collecting the campaign CSVs."""
import csv
import re
from collections import defaultdict
from statistics import median
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.ticker import ScalarFormatter

OUT = Path(__file__).resolve().parent / "out" / "topozoo"
COLORS = {"KATch2-synth": "#176c49", "PCSat / all": "#155da1", "PCSat / ctx": "#b56613",
          "PCSat / proj": "#71418f", "PCSat / generic": "#74655c", "PCSat / paths": "#b56613",
          "Translate + solve": "#aa405d"}


def load(*files):
    rows = {}
    for name in files:
        with (OUT / name).open(encoding="utf-8") as f:
            for row in csv.DictReader(f):
                nodes = re.search(r"V=(\d+)", row["instance"])
                if nodes:
                    row["nodes"] = int(nodes[1])
                    rows[row["instance"], row["tool"], row["preset"]] = row
    return list(rows.values())


def panel(ax, rows, title, keys):
    for label in keys:
        points = []
        for row in rows:
            series = "KATch2-synth" if row["tool"] == "katch2" else "PCSat / " + row["preset"]
            elapsed = row["ms"]
            verdict = row["verdict"]
            if label == "Translate + solve":
                translation = row.get("translation_ms", "")
                if series != "PCSat / all" or not translation.isdigit() or verdict not in ("sat", "unsat"):
                    continue
                elapsed = int(translation) + int(elapsed)
            elif label != series or verdict not in ("sat", "unsat", "timeout"):
                continue
            points.append((row["nodes"], int(elapsed) / 1000, verdict == "timeout"))
        if not points:
            continue
        points.sort()
        color = COLORS[label]
        ax.plot([x for x, _, _ in points], [float("nan") if t else y for _, y, t in points],
                color=color, label=label, lw=1.25, marker="o", ms=3.8)
        ax.scatter([x for x, _, t in points if t], [y for _, y, t in points if t],
                   color=color, marker="x", s=27)
    cutoffs = [r["nodes"] for r in rows
               if r["preset"] == "all" and r["verdict"] == "translation_timeout"]
    if cutoffs:
        ax.scatter(cutoffs, [120] * len(cutoffs), color=COLORS["PCSat / all"],
                   marker="^", facecolors="none", label="Translation cutoff (120 s)")
    ax.set(xscale="log", yscale="log", title=title, xlabel="Switches", ylabel="Elapsed time (s)")
    ax.set_xticks([4, 10, 25, 68, 110, 197])
    ax.xaxis.set_major_formatter(ScalarFormatter())
    ax.grid(axis="y", alpha=.2)
    ax.spines[["right", "top"]].set_visible(False)
    ax.legend(fontsize=8, frameon=False)


def main():
    standard = load("campaign_standard.csv", "campaign_big_std.csv", "campaign_cogentco_retry.csv")
    hard = load("campaign_big_hard.csv")
    star = load("campaign_star.csv", "campaign_big_star.csv")
    # Replace the initial large-graph reference timings with medians from
    # the release binary rebuilt from the benchmark checkout.
    runs = defaultdict(list)
    with (OUT / "large_katch2_rebuilt.csv").open() as f:
        for row in csv.DictReader(f):
            if row["verdict"] in ("sat", "unsat"):
                runs[row["suite"], row["instance"]].append(int(row["ms"]))
    for suite, rows in [("std", standard), ("hard", hard), ("star", star)]:
        for row in rows:
            times = runs.get((suite, row["instance"]))
            if row["tool"] == "katch2" and times:
                row["ms"] = str(round(median(times)))
    # For Cogentco, the optimized preset was repeated on the same SMT input.
    repeats = defaultdict(list)
    with (OUT / "cogentco_pcsat_repeats.csv").open() as f:
        for row in csv.DictReader(f):
            if row["verdict"] == "sat":
                repeats[row["suite"]].append(int(row["ms"]))
    for suite, rows in [("std", standard), ("star", star)]:
        for row in rows:
            if row["nodes"] == 197 and row["preset"] == "all" and repeats[suite]:
                row["ms"] = str(round(median(repeats[suite])))
                row["verdict"] = "sat"
    suites = [
        ("fig1_topozoo_scaling", [
            (standard, "Unfolded paths / 1 blocked, 3 required",
             ["KATch2-synth", "PCSat / generic", "PCSat / ctx", "PCSat / proj", "PCSat / all"]),
            (hard, "Unfolded paths / 3 blocked, 10 required", ["KATch2-synth", "PCSat / all"])]),
        ("fig2_topozoo_star_and_translation", [
            (star, "Kleene star / 1 blocked, 2 required",
             ["KATch2-synth", "PCSat / paths", "PCSat / all"]),
            (standard, "Standard suite / cost of translation",
             ["KATch2-synth", "PCSat / all", "Translate + solve"])])]
    for stem, panels in suites:
        fig, axes = plt.subplots(1, 2, figsize=(11, 4.5), layout="constrained")
        for ax, (rows, title, keys) in zip(axes, panels):
            panel(ax, rows, title, keys)
        fig.supxlabel("Crosses mark solver timeouts. Missing measurements are omitted. Both axes use logarithmic scales.", fontsize=9)
        for ext in ("png", "pdf"):
            fig.savefig(OUT / f"{stem}.{ext}", dpi=180)
        plt.close(fig)
    gallery = "\n".join(
        f'<figure><img src="{stem}.png" alt="{panels[0][1]} and {panels[1][1]}"></figure>'
        for stem, panels in suites
    )
    (OUT / "comparison_charts.html").write_text(
        '<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" '
        'content="width=device-width, initial-scale=1"><title>Topology Zoo benchmarks</title>'
        '<style>body{max-width:1100px;margin:auto;padding:16px;font:16px system-ui}figure{margin:1em 0}'
        'img{display:block;width:100%;height:auto}</style><h1>Topology Zoo benchmarks</h1>'
        + gallery + '</html>', encoding="utf-8")


if __name__ == "__main__":
    main()
