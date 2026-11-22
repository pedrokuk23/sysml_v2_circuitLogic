"""Scalability sweep (bench_scale.json values) as two small multiples with one y-axis each (dataviz skill):
(a) run time of the three checks, log scale, direct-labeled, marker shape as secondary encoding;
(b) and-inverter-graph size after optimization. Palette slots 1-3 validated all-pairs (light)."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

INK, INK2, GRID = "#0b0b0b", "#52514e", "#e4e3df"
C1, C2, C3 = "#2a78d6", "#eb6834", "#1baf7a"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 7, "pdf.fonttype": 42, "axes.edgecolor": INK2,
                     "axes.labelcolor": INK, "xtick.color": INK2, "ytick.color": INK2, "axes.linewidth": 0.6})
R = [10, 25, 50, 100, 200, 400]
SB = ["8/8", "8/8", "8/8", "16/10", "16/10", "32/12"]
confl = [5, 19, 93, 220, 897, 1999]
generic = [0.37, 2.3, 9.5, 40.3, None, None]
circuit = [0.07, 0.40, 1.7, 7.5, 31.6, 133.4]
yosys = [0.3, 0.3, 0.3, 0.5, 0.7, 1.2]
aig = [47, 96, 162, 329, 586, 1192]

fig, (a, b) = plt.subplots(2, 1, figsize=(3.45, 3.35), gridspec_kw=dict(height_ratios=[1.6, 1], hspace=0.55))
fig.subplots_adjust(left=0.2, right=0.95, top=0.95, bottom=0.17)
for ax in (a, b):
    ax.set_xscale("log"); ax.set_xticks(R); ax.set_xticklabels([str(r) for r in R])
    ax.minorticks_off(); ax.grid(axis="y", color=GRID, lw=0.5); ax.set_axisbelow(True)
    for sp in ("top", "right"): ax.spines[sp].set_visible(False)
    ax.tick_params(length=2, width=0.5)
xs_g = [r for r, g in zip(R, generic) if g]; g = [x for x in generic if x]
a.plot(xs_g, g, "-o", color=C1, lw=1.6, ms=4, mec="white", mew=0.6, label="quantified test (4); not run past 100")
a.plot(R, circuit, "-s", color=C2, lw=1.6, ms=4, mec="white", mew=0.6, label="pairwise overlap (Proposition 1)")
a.plot(R, yosys, "-^", color=C3, lw=1.6, ms=4.5, mec="white", mew=0.6, label="Yosys proof of all requirements")
a.set_yscale("log"); a.set_ylabel("time (s)"); a.set_ylim(0.04, 3000)
a.text(R[-1], yosys[-1] * 1.6, "1.2 s", ha="center", va="bottom", fontsize=6.2, color=INK2)
a.text(R[-1], circuit[-1] * 1.6, "133 s", ha="center", va="bottom", fontsize=6.2, color=INK2)
a.text(xs_g[-1] * 1.12, g[-1], "40 s", ha="left", va="center", fontsize=6.2, color=INK2)
a.legend(loc="upper left", frameon=False, fontsize=6.3, handlelength=2.2, borderaxespad=0.2, labelcolor=INK)
a.set_title("(a) Conflict detection and proof time", fontsize=7, loc="left", color=INK, fontweight="bold")
b.plot(R, aig, "-o", color=C1, lw=1.6, ms=4, mec="white", mew=0.6)
b.set_ylabel("AND gates"); b.set_ylim(0, 1400)
b.text(R[-1] * 0.9, aig[-1], "1192", ha="right", va="center", fontsize=6.4, color=INK)
b.set_title("(b) Requirement circuit after optimization", fontsize=7, loc="left", color=INK, fontweight="bold")
b.set_xticklabels([f"{r}\n{sb}\n{c}" for r, sb, c in zip(R, SB, confl)])
b.text(-0.06, -0.33, "R\nS/B\nconflicts", transform=b.transAxes, ha="right", va="center", fontsize=6.4, color=INK2,
       linespacing=1.18)
b.set_xlabel("")
fig.savefig("fig_scale.pdf"); fig.savefig("fig_scale.png", dpi=300)
