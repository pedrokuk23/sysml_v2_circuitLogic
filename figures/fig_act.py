"""FireSat detection-and-report action flow drawn as a logic view (decision = multiplexer, join = AND, merge = OR).
Hand-placed layout; the defect is marked in red with a warning sign and a written explanation."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Polygon, Circle

INK, INK2, CRIT = "#0b0b0b", "#52514e", "#d03b3b"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 7, "pdf.fonttype": 42})
W, H = 7.64, 2.65
fig = plt.figure(figsize=(W, H)); ax = fig.add_axes([0, 0, 1, 1]); ax.set_xlim(0, W); ax.set_ylim(-0.5, H - 0.5)
ax.set_axis_off()
Y, YT, YB = 0.95, 1.55, 0.35


def box(x, y, txt, w=0.7, h=0.44):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0,rounding_size=0.07", fc="white",
                                ec=INK, lw=0.8, zorder=3))
    ax.text(x, y, txt, ha="center", va="center", fontsize=9.6, color=INK, zorder=4, linespacing=1.1)
    return (x - w / 2, x + w / 2)


def mux(x, y, txt, bad=False):
    w, h = 0.86, 0.52
    ax.add_patch(Polygon([(x - w / 2, y + h / 2), (x + w / 2, y + h / 2), (x + w / 3.4, y - h / 2), (x - w / 3.4, y - h / 2)],
                         closed=True, fc="white", ec=CRIT if bad else INK, lw=1.8 if bad else 0.8, zorder=3))
    ax.text(x, y + 0.03, txt, ha="center", va="center", fontsize=8.8, color=INK, zorder=4, linespacing=1.05)


def bar(x, y, lab=None, h=0.95):
    ax.add_patch(plt.Rectangle((x - 0.03, y - h / 2), 0.06, h, color=INK, zorder=3))
    if lab:
        ax.text(x, y + h / 2 + 0.04, lab, ha="center", va="bottom", fontsize=9.6, color=INK, fontweight="bold")


def arrow(pts, lab=None, lpos=None, color=INK2, ha="center"):
    xs, ys = zip(*pts)
    ax.plot(xs[:-1] + (xs[-1],), ys, color=color, lw=0.9, zorder=2, solid_joinstyle="round")
    (x0, y0), (x1, y1) = pts[-2], pts[-1]
    ax.annotate("", xy=(x1, y1), xytext=(x0 + 0.8 * (x1 - x0), y0 + 0.8 * (y1 - y0)),
                arrowprops=dict(arrowstyle="-|>", color=color, lw=0.9, mutation_scale=7), zorder=2)
    if lab:
        ax.text(*lpos, lab, ha=ha, va="bottom", fontsize=9.5, color=INK)


# nodes
ax.add_patch(Circle((0.18, Y), 0.07, color=INK, zorder=3))
ax.add_patch(Circle((7.52, Y), 0.08, fc="white", ec=INK, lw=0.9, zorder=3)); ax.add_patch(Circle((7.52, Y), 0.05, color=INK, zorder=4))
box(0.72, Y, "observe\n1 min"); box(1.5, Y, "detect\n2 min"); mux(2.3, Y, "MUX\nfireCheck")
box(3.50, Y, "geolocate\n1 min", w=0.7); bar(4.12, Y, "fork")
ax.add_patch(Circle((4.52, YB + 0.25), 0.13, fc="white", ec=INK, lw=0.8, zorder=3))
ax.text(4.52, YB + 0.25, "≥1", ha="center", va="center", fontsize=9.30, color=INK, zorder=4)
box(5.15, YB + 0.25, "downlink\n1 min"); mux(5.95, YB + 0.25, "MUX ⚠\nlinkCheck", bad=True)
box(5.15, YT, "archive\n1 min"); box(5.95, -0.2, "retry\n3 min")
bar(6.87, Y + 0.05, "&", h=1.25); box(7.19, Y, "notify\n1 min", w=0.48)
# edges
arrow([(0.25, Y), (0.41, Y)]); arrow([(1.03, Y), (1.19, Y)]); arrow([(1.81, Y), (1.94, Y)])
arrow([(2.62, Y), (3.15, Y)], "fire", (2.85, Y + 0.03))
arrow([(2.3, Y + 0.22), (2.3, 1.95), (7.52, 1.95), (7.52, Y + 0.08)], "¬fire", (5.00, 1.96))
arrow([(3.85, Y), (4.09, Y)])
arrow([(4.15, Y + 0.3), (4.40, YT), (4.84, YT)]); arrow([(5.50, YT), (6.84, YT)])
arrow([(4.15, Y - 0.3), (4.39, YB + 0.25)]); arrow([(4.65, YB + 0.25), (4.84, YB + 0.25)])
arrow([(5.46, YB + 0.25), (5.58, YB + 0.25)])
arrow([(6.35, YB + 0.25), (6.84, YB + 0.25)]); ax.text(6.60, YB + 0.28, "linkUp", ha="center", va="bottom", fontsize=9.30, color=INK)
arrow([(5.95, YB + 0.02), (5.95, -0.02)]); ax.text(6.02, YB - 0.1, "linkUp ∧ backlog", ha="left", va="center", fontsize=9.30, color=INK)
arrow([(5.64, -0.2), (4.52, -0.2), (4.52, YB + 0.12)])
arrow([(6.90, Y), (6.95, Y)]); arrow([(7.43, Y), (7.44, Y)])
ax.text(0.2, 0.55, "Nominal cycle 6 min;\n+4 min per retry loop.", ha="left", va="center", fontsize=9.30, color=INK2)
fig.savefig("fig_act.pdf"); fig.savefig("fig_act.png", dpi=250)
