"""FireSat detection-and-report action flow drawn as a logic view (decision = multiplexer, join = AND, merge = OR).
Hand-placed so that every label is readable at full page width; text in ink, the defect in status-critical red with
an icon and a written explanation (dataviz skill: never color alone)."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch, Polygon, Circle

INK, INK2, CRIT = "#0b0b0b", "#52514e", "#d03b3b"
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 7, "pdf.fonttype": 42})
W, H = 7.16, 2.9
fig = plt.figure(figsize=(W, H)); ax = fig.add_axes([0, 0, 1, 1]); ax.set_xlim(0, W); ax.set_ylim(-0.82, H - 0.82)
ax.set_axis_off()
Y, YT, YB = 0.95, 1.55, 0.35


def box(x, y, txt, w=0.62, h=0.36):
    ax.add_patch(FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle="round,pad=0,rounding_size=0.07", fc="white",
                                ec=INK, lw=0.8, zorder=3))
    ax.text(x, y, txt, ha="center", va="center", fontsize=7, color=INK, zorder=4, linespacing=1.1)
    return (x - w / 2, x + w / 2)


def mux(x, y, txt, bad=False):
    w, h = 0.74, 0.46
    ax.add_patch(Polygon([(x - w / 2, y + h / 2), (x + w / 2, y + h / 2), (x + w / 3.4, y - h / 2), (x - w / 3.4, y - h / 2)],
                         closed=True, fc="white", ec=CRIT if bad else INK, lw=1.8 if bad else 0.8, zorder=3))
    ax.text(x, y + 0.03, txt, ha="center", va="center", fontsize=6.6, color=INK, zorder=4, linespacing=1.05)


def bar(x, y, lab=None, h=0.95):
    ax.add_patch(plt.Rectangle((x - 0.03, y - h / 2), 0.06, h, color=INK, zorder=3))
    if lab:
        ax.text(x, y + h / 2 + 0.04, lab, ha="center", va="bottom", fontsize=7, color=INK, fontweight="bold")


def arrow(pts, lab=None, lpos=None, color=INK2, ha="center"):
    xs, ys = zip(*pts)
    ax.plot(xs[:-1] + (xs[-1],), ys, color=color, lw=0.9, zorder=2, solid_joinstyle="round")
    (x0, y0), (x1, y1) = pts[-2], pts[-1]
    ax.annotate("", xy=(x1, y1), xytext=(x0 + 0.8 * (x1 - x0), y0 + 0.8 * (y1 - y0)),
                arrowprops=dict(arrowstyle="-|>", color=color, lw=0.9, mutation_scale=7), zorder=2)
    if lab:
        ax.text(*lpos, lab, ha=ha, va="bottom", fontsize=6.6, color=INK)


# nodes
ax.add_patch(Circle((0.18, Y), 0.07, color=INK, zorder=3))
ax.add_patch(Circle((6.99, Y), 0.08, fc="white", ec=INK, lw=0.9, zorder=3)); ax.add_patch(Circle((6.99, Y), 0.05, color=INK, zorder=4))
box(0.72, Y, "observe\n1 min"); box(1.5, Y, "detect\n2 min"); mux(2.3, Y, "MUX\nfireCheck")
box(3.1, Y, "geolocate\n1 min", w=0.7); bar(3.72, Y, "fork")
ax.add_patch(Circle((4.12, YB + 0.25), 0.13, fc="white", ec=INK, lw=0.8, zorder=3))
ax.text(4.12, YB + 0.25, "≥1", ha="center", va="center", fontsize=6.6, color=INK, zorder=4)
box(4.75, YB + 0.25, "downlink\n1 min"); mux(5.55, YB + 0.25, "MUX ⚠\nlinkCheck", bad=True)
box(4.75, YT, "archive\n1 min"); box(5.55, -0.2, "retry\n3 min")
bar(6.27, Y + 0.05, "&", h=1.25); box(6.62, Y, "notify\n1 min", w=0.46)
# edges
arrow([(0.25, Y), (0.41, Y)]); arrow([(1.03, Y), (1.19, Y)]); arrow([(1.81, Y), (1.94, Y)])
arrow([(2.62, Y), (2.75, Y)], "fire", (2.69, Y + 0.25))
arrow([(2.3, Y + 0.22), (2.3, 1.95), (6.99, 1.95), (6.99, Y + 0.08)], "¬fire", (4.6, 1.96))
arrow([(3.45, Y), (3.69, Y)])
arrow([(3.75, Y + 0.3), (4.0, YT), (4.44, YT)]); arrow([(5.06, YT), (6.24, YT)])
arrow([(3.75, Y - 0.3), (3.99, YB + 0.25)]); arrow([(4.25, YB + 0.25), (4.44, YB + 0.25)])
arrow([(5.06, YB + 0.25), (5.18, YB + 0.25)])
arrow([(5.92, YB + 0.25), (6.24, YB + 0.25)]); ax.text(6.08, YB + 0.28, "linkUp", ha="center", va="bottom", fontsize=6.6, color=INK)
arrow([(5.55, YB + 0.02), (5.55, -0.02)]); ax.text(5.62, YB - 0.1, "linkUp ∧ backlog", ha="left", va="center", fontsize=6.6, color=INK)
arrow([(5.24, -0.2), (4.12, -0.2), (4.12, YB + 0.12)])
arrow([(6.3, Y), (6.39, Y)]); arrow([(6.85, Y), (6.9, Y)])
# findings (text in ink; icon + red rule mark the defect)
ax.plot([0.12, 0.12], [-0.47, -0.78], color=CRIT, lw=1.8)
ax.text(0.2, -0.48, "⚠ linkCheck: no branch for ¬linkUp (selection incomplete); linkUp ∧ backlog enables both branches (not one-hot).",
        ha="left", va="top", fontsize=6.6, color=INK)
ax.text(0.2, -0.65, "Token game over the 8 valuations of (fire, linkUp, backlog): deadlock in 2, possible endless retry in 1.",
        ha="left", va="top", fontsize=6.6, color=INK)
ax.text(0.2, 0.55, "Nominal cycle 6 min;\n+4 min per retry loop.", ha="left", va="center", fontsize=6.6, color=INK2)
fig.savefig("fig_act.pdf"); fig.savefig("fig_act.png", dpi=250)
