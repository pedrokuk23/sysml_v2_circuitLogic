"""Scalability sweep (values of bench_scale.json): run time of the conflict checks and of the Yosys proof, log scale,
direct labels, marker shape as a second encoding."""
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

fig, a = plt.subplots(1, 1, figsize=(4.48, 3.4))
plt.rcParams.update({"font.size": 8})
fig.subplots_adjust(left=0.13, right=0.97, top=0.76, bottom=0.21)
a.set_xscale("log"); a.set_xticks(R); a.minorticks_off(); a.grid(axis="y", color=GRID, lw=0.5); a.set_axisbelow(True)
for sp in ("top", "right"): a.spines[sp].set_visible(False)
a.tick_params(length=2, width=0.5, labelsize=8)
xs_g = [r for r, g in zip(R, generic) if g]; g = [x for x in generic if x]
a.plot(xs_g, g, "-o", color=C1, lw=1.6, ms=4.5, mec="white", mew=0.6, label="quantified test (3), up to R = 100")
a.plot(R, circuit, "-s", color=C2, lw=1.6, ms=4.5, mec="white", mew=0.6, label="overlap test (Proposition 1)")
a.plot(R, yosys, "-^", color=C3, lw=1.6, ms=5, mec="white", mew=0.6, label="Yosys check of all requirements")
a.set_yscale("log"); a.set_ylabel("time (s)", fontsize=8); a.set_ylim(0.04, 400)
a.text(R[-1], yosys[-1] * 1.6, "1.2 s", ha="center", va="bottom", fontsize=8, color=INK2)
a.text(R[-1], circuit[-1] * 1.6, "133 s", ha="center", va="bottom", fontsize=8, color=INK2)
a.text(xs_g[-1] * 1.12, g[-1], "40 s", ha="left", va="center", fontsize=8, color=INK2)
a.legend(loc="lower left", bbox_to_anchor=(0.0, 1.02), frameon=False, fontsize=8, handlelength=2.2, borderaxespad=0.0, labelcolor=INK)
a.set_xticklabels([f"{r}\n{sb}\n{c}" for r, sb, c in zip(R, SB, confl)])
a.text(-0.02, -0.15, "R\nS/B\nconflicts", transform=a.transAxes, ha="right", va="center", fontsize=8, color=INK2,
       linespacing=1.18)
fig.savefig("fig_scale.pdf"); fig.savefig("fig_scale.png", dpi=200)
