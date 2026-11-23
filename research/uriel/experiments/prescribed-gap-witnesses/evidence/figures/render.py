"""Regenerate the two vector figures with Python 3.11+ and Matplotlib 3.7+."""
import json
import math
from fractions import Fraction
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib import ticker

HERE = Path(__file__).resolve().parent
INK, MUTED = "#152B3B", "#445564"
BLUE, GREEN, RED = "#35658A", "#127666", "#A34532"
PALE, FAINT = "#E3EBEF", "#EEF4F4"
META = {"CreationDate": None, "ModDate": None, "Creator": "Reproducible research figures"}
plt.rcParams.update({
    "font.family": "DejaVu Sans", "font.size": 9, "axes.edgecolor": MUTED,
    "text.color": INK, "axes.labelcolor": INK, "xtick.color": MUTED, "ytick.color": MUTED,
    "axes.linewidth": .7, "pdf.fonttype": 42, "mathtext.fontset": "dejavusans",
})


def load(part):
    return json.loads((HERE.parent / part / "results.json").read_text())


def midpoint(bracket):
    return sum(map(float, bracket)) / 2


def axis(ax, title, ticks):
    ax.spines[["top", "right"]].set_visible(False)
    ax.set_axisbelow(True)
    ax.grid(axis="y", color=PALE, linewidth=.65)
    ax.tick_params(length=3, width=.7)
    ax.set_title(title, fontsize=11.3, weight="semibold", loc="left", pad=10)
    ax.set_xticks(ticks)
    ax.set_xlabel("Ordinate $x$")


def scalar():
    data = load("scalar")
    case = next(c for c in data["cases"] if c["mode"] == "genuine" and c["include_nine"])
    prime_powers = [(int(n), math.log(p)) for n, p in data["prime_powers"].items()]
    gamma = midpoint(data["gamma_fast"])
    peak_x = midpoint(case["segments"][-1]["critical_bracket"])
    peak_y = midpoint(case["normalized_candidates"]["critical in (11,12)"])
    level = float(Fraction(data["post_hoc_subinterval"]["ceiling"]))

    def normalized(x):
        ramp = sum(log_p * (x / n - 1) for n, log_p in prime_powers if n <= x)
        return (ramp - x * math.log(x) + (1 + gamma) * x) / math.sqrt(x)

    for record in data["integer_controls"]:
        assert abs(normalized(record["x"]) - midpoint(record["normalized"])) < 1e-12
    assert abs(normalized(peak_x) - peak_y) < 1e-12
    assert normalized(11) < level < peak_y and normalized(12) < level

    fig, (overall, detail) = plt.subplots(1, 2, figsize=(8.5, 3.4))
    fig.subplots_adjust(left=.089, right=.982, bottom=.17, top=.82, wspace=.36)
    axis(overall, "Full prescribed interval", [8, 9, 10, 11, 12])
    axis(detail, "Interior peak near 11", [11, 11.1, 11.2, 11.3])
    overall.set_ylabel(r"$H(x)=G(x)/\sqrt{x}$")
    for ax, lo, hi in ((overall, 8, 12), (detail, 11, 11.31)):
        points = sorted({lo + (hi - lo) * i / 480 for i in range(481)} |
                        {x for x in (8, 9, 11, peak_x, 12) if lo <= x <= hi})
        ax.plot(points, [normalized(x) for x in points], color=BLUE, linewidth=2.0, zorder=3)
    overall.set_xlim(7.95, 12.05)
    overall.set_ylim(.519, .679)
    overall.set_yticks([.53, .56, .59, .62, .65])
    overall.axvspan(11, 11.31, color=FAINT, zorder=0)
    overall.axhline(2 / 3, color=MUTED, linestyle=(0, (3, 3)), linewidth=1)
    overall.text(11.91, 2 / 3 + .0022, "proved upper bound  2/3", fontsize=8.2, ha="right")
    for x in [8, 9, 11, 12]:
        overall.plot(x, normalized(x), "o", ms=4, color=BLUE)
    overall.annotate("0.646809", (8, normalized(8)), xytext=(6, 2),
                     textcoords="offset points", fontsize=8)
    overall.annotate("0.528129", (12, normalized(12)), xytext=(-6, -9),
                     ha="right", textcoords="offset points", fontsize=8)
    detail.set_xlim(10.995, 11.313)
    detail.set_ylim(.53695, .53748)
    detail.set_yticks([.5370, .5371, .5372, .5373, .5374])
    detail.xaxis.set_major_formatter(ticker.StrMethodFormatter("{x:g}"))
    detail.yaxis.set_major_formatter(ticker.StrMethodFormatter("{x:.4f}"))
    detail.axhline(level, color=RED, linewidth=1.1, linestyle=(0, (3, 2)))
    detail.text(11.307, level + .000007, "post hoc  0.5373", color=RED, fontsize=8,
                ha="right", va="bottom", bbox={"fc":"white","ec":"none","pad":1})
    detail.plot(peak_x, peak_y, "o", ms=4.7, color=GREEN, zorder=4)
    detail.annotate("0.537401 at 11.126185", (peak_x, peak_y), xytext=(0, 10),
                    ha="center", textcoords="offset points", fontsize=8)
    detail.plot(11, normalized(11), "o", ms=4, color=BLUE)
    fig.savefig(HERE / "scalar.pdf", metadata=META)
    plt.close(fig)


def positive_labels(prime, centers, cutoff):
    modulus = prime
    while modulus <= cutoff:
        modulus *= prime
    return {c % modulus for c in centers if 1 <= c % modulus <= cutoff}


def handoff():
    data = load("stitch")
    assert data["target"] == [8, 12] and data["Ct"] == 2 and data["eta"] == 1
    controls = data["controls"]
    hole = next(row for row in controls if row["left"] == [80] and row["right"] == [11])
    seam = next(row for row in controls if row["left"] == [99] and row["right"] == [10])
    assert not hole["covered"] and hole["left_first_failure"] == "9" and hole["right_first_success"] == "11"
    assert seam["covered"] and not seam["common_point"] and seam["left_first_failure"] == seam["right_first_success"] == "10"
    # Genuine strict cutoff-rule example in the elementary integral 3-adic model.
    centers = (8, 169)
    early = positive_labels(3, centers, 64)
    late = positive_labels(3, centers, 144)
    assert early == {7, 8} and late == {8} and max(late) <= 8
    fig, ax = plt.subplots(figsize=(8.5, 3.75))
    fig.subplots_adjust(left=.34, right=.965, top=.91, bottom=.16)
    ax.set_xlim(7.88, 12.10)
    ax.set_ylim(-.55, 3.76)
    ax.grid(axis="x", color=PALE, linewidth=.65)
    ax.set_xticks([8, 9, 10, 11, 12])
    ax.set_yticks([])
    ax.spines[["top", "right", "left"]].set_visible(False)
    ax.tick_params(length=3, width=.7)
    ax.set_xlabel(r"Ordinate $x$ on the fixed target")
    trans = ax.get_yaxis_transform()

    def left(y, title, desc):
        ax.text(-.49, y+.085, title, fontsize=10.5, weight="semibold", va="bottom", transform=trans)
        ax.text(-.49, y-.065, desc, fontsize=8.5, va="top", color=MUTED, transform=trans)

    def bar(x1, x2, y, color, *, closed_right=True):
        ax.plot([x1, x2], [y, y], lw=2.9, color=color, solid_capstyle="butt", zorder=3)
        for x, closed in ((x1, True), (x2, closed_right)):
            ax.plot(x, y, marker="o", ms=5.6, mec=color, mew=1.3,
                    mfc=color if closed else "white", zorder=4)

    left(3.05, "One center tuple", r"$E_{64}=\{7,8\},\quad E_{144}=\{8\}$")
    bar(8, 12, 3.05, GREEN)
    ax.text(10, 3.24, "later screen passes everywhere", ha="center", color=GREEN, fontsize=8.4)
    left(1.9, "Two lists, exact handoff", r"Left $\{99\}$, right $\{10\}$")
    bar(8, 10, 2.03, BLUE, closed_right=False)
    bar(10, 12, 1.78, GREEN)
    ax.text(8.95, 2.15, "left passes", ha="center", va="bottom", color=BLUE, fontsize=8.4)
    ax.text(11.05, 1.94, "right passes", ha="center", va="bottom", color=GREEN, fontsize=8.4)
    left(.62, "Two lists, missed interval", r"Left $\{80\}$, right $\{11\}$")
    bar(8, 9, .75, BLUE, closed_right=False)
    bar(11, 12, .50, GREEN)
    ax.fill_between([9, 11], .35, .90, color="#FAE9E4", zorder=1)
    ax.text(10, .62, r"neither passes on $[9,11)$", color=RED, ha="center", va="center", fontsize=8.6)
    ax.text(10, -.23, "Filled point = included       Hollow point = excluded",
            ha="center", va="center", color=MUTED, fontsize=8)
    fig.savefig(HERE / "handoff.pdf", metadata=META)
    plt.close(fig)


if __name__ == "__main__":
    scalar()
    handoff()
