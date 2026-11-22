"""Requirements of the Lockheed Martin state machines drawn as programmable-logic arrays (PLA).

Each row is one requirement (an AND gate). Columns on the left are input literals: a filled dot means the literal
appears true in the antecedent, an open circle means it appears negated. Columns on the right are the lines of the
next-state bus: a dot shows which line the gate drives. Conflicts (bus contention) are bracketed in red with an
icon and a label; holes (undriven situations) are listed under each panel. Text is always in ink, never in the
series color (dataviz skill rule)."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

INK, INK2, GRID = "#0b0b0b", "#52514e", "#b9b8b3"
BLUE = "#2a78d6"            # categorical slot 1: drive dots / outputs
CRIT = "#d03b3b"            # status critical: conflict (always with icon + label)
WARN_EDGE = "#c98500"       # warning, darker step for line work on white
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 7, "pdf.fonttype": 42})

AP = dict(
    title="(a) Autopilot",
    inputs=["state=T", "state=N", "state=M", "state=S", "standby", "good", "supported", "apfail"],
    outputs=["T", "N", "M", "S"],
    rows=[("FSM-002", {"state=T": 1, "standby": 1}, "S"),
          ("FSM-003", {"state=T": 1, "good": 1, "supported": 1}, "N"),
          ("FSM-004", {"state=N": 1, "good": 0}, "M"),
          ("FSM-005", {"state=N": 1, "standby": 1}, "S"),
          ("FSM-006", {"state=M": 1, "standby": 1, "good": 1}, "S"),
          ("FSM-007", {"state=M": 1, "supported": 1, "good": 1}, "T"),
          ("FSM-008", {"state=S": 1, "standby": 0}, "T"),
          ("FSM-009", {"state=S": 1, "apfail": 1}, "M")],
    conflicts=[(0, 1, "C1", "in T: standby ∧ good ∧ supported"),
               (2, 3, "C2", "in N: standby ∧ ¬good"),
               (4, 5, "C3", "in M: standby ∧ good ∧ supported"),
               (6, 7, "C4", "in S: apfail ∧ ¬standby")],
    holes=[("T", "6/16", "(¬good ∧ ¬standby) ∨ (¬standby ∧ ¬supported)"),
           ("N", "4/16", "good ∧ ¬standby"),
           ("M", "10/16", "¬good ∨ (¬standby ∧ ¬supported)"),
           ("S", "4/16", "standby ∧ ¬apfail")])

SEN = dict(
    title="(b) Sensor",
    inputs=["state=Nom", "state=Tr", "state=F", "limits", "request", "mode"],
    outputs=["Nom", "Tr", "F"],
    rows=[("FSM-010", {"state=Nom": 1, "limits": 1}, "F"),
          ("FSM-011", {"state=Nom": 1, "request": 0}, "Tr"),
          ("FSM-012", {"state=F": 1, "request": 0, "limits": 0}, "Tr"),
          ("FSM-013", {"state=Tr": 1, "request": 1, "mode": 1}, "Nom")],
    conflicts=[(0, 1, "C5", "in Nom: limits ∧ ¬request")],
    holes=[("Nom", "2/8", "request ∧ ¬limits"),
           ("Tr", "6/8", "¬mode ∨ ¬request"),
           ("F", "6/8", "limits ∨ request")])


def panel(ax, M, x0=0.0, ytop=0.0):
    ni, no, nr = len(M["inputs"]), len(M["outputs"]), len(M["rows"])
    dx, dy = 1.0, 1.0
    xin = [x0 + 3.3 + k * dx for k in range(ni)]
    xg = xin[-1] + 1.3
    xout = [xg + 1.4 + k * dx for k in range(no)]
    yrow = [ytop - 1.0 - r * dy for r in range(nr)]
    ybot = yrow[-1] - 0.6
    ax.text(x0, ytop + 2.9, M["title"], ha="left", va="bottom", fontsize=7.5, fontweight="bold", color=INK)
    for x, n in zip(xin, M["inputs"]):
        ax.text(x, ytop + 0.2, n, rotation=55, ha="left", va="bottom", fontsize=6.5, color=INK)
        ax.plot([x, x], [ytop, ybot], color=GRID, lw=0.6, zorder=1)
    ax.text((xin[0] + xin[-1]) / 2, ybot - 0.2, "input literals", ha="center", va="top", fontsize=6.3, color=INK2)
    for x, n in zip(xout, M["outputs"]):
        ax.text(x, ytop + 0.2, f"next={n}", rotation=55, ha="left", va="bottom", fontsize=6.5, color=INK)
        ax.plot([x, x], [ytop, ybot], color=BLUE, lw=0.8, alpha=0.45, zorder=1)
    ax.text((xout[0] + xout[-1]) / 2, ybot - 0.2, "next-state bus", ha="center", va="top", fontsize=6.3, color=INK2)
    for (name, lits, out), y in zip(M["rows"], yrow):
        ax.text(x0 + 2.9, y, name, ha="right", va="center", fontsize=6.8, color=INK)
        ax.plot([xin[0] - 0.3, xg - 0.36], [y, y], color=INK2, lw=0.6, zorder=1)
        for x, n in zip(xin, M["inputs"]):
            if n in lits:
                if lits[n]:
                    ax.plot(x, y, "o", ms=4.2, color=INK, zorder=3)
                else:
                    ax.plot(x, y, "o", ms=4.2, mfc="white", mec=INK, mew=0.9, zorder=3)
        ax.add_patch(FancyBboxPatch((xg - 0.36, y - 0.4), 0.72, 0.8, boxstyle="round,pad=0.0,rounding_size=0.15",
                                    fc="white", ec=INK, lw=0.8, zorder=3))
        ax.text(xg, y, "&", ha="center", va="center", fontsize=7, fontweight="bold", color=INK, zorder=4)
        xo = xout[M["outputs"].index(out)]
        ax.plot([xg + 0.36, xo], [y, y], color=BLUE, lw=1.2, zorder=2)
        ax.plot(xo, y, "o", ms=4.6, color=BLUE, mec="white", mew=0.8, zorder=3)
    xb = xout[-1] + 0.7
    for i, j, tag, region in M["conflicts"]:
        y1, y2 = yrow[i], yrow[j]
        ax.plot([xb, xb + 0.25, xb + 0.25, xb], [y1, y1, y2, y2], color=CRIT, lw=1.3, zorder=2)
        ax.text(xb + 0.5, (y1 + y2) / 2, f"⚠ {tag} conflict\n{region}", ha="left", va="center", fontsize=6.3,
                color=INK, linespacing=1.2)
    xh = 28.3
    ax.text(xh, yrow[0] + 0.1, "Holes (no gate drives the bus;\nthe SysML stay rule holds the state)", ha="left",
            va="center", fontsize=6.3, color=INK, fontweight="bold", linespacing=1.2)
    for k, (st, frac, cond) in enumerate(M["holes"]):
        yy = yrow[0] - 1.25 - 1.25 * k
        ax.plot([xh, xh + 0.45], [yy + 0.25, yy + 0.25], color=WARN_EDGE, lw=2.2, ls=(0, (1.5, 1)))
        ax.text(xh + 0.65, yy + 0.25, f"in {st}: {frac} situations", ha="left", va="center", fontsize=6.3, color=INK)
        ax.text(xh + 0.65, yy - 0.3, cond, ha="left", va="center", fontsize=6.3, color=INK2)
    return ybot - 0.9


fig = plt.figure(figsize=(7.16, 4.0))
ax = fig.add_axes([0, 0, 1, 1]); ax.set_axis_off()
b1 = panel(ax, AP, 0.0, 0.0)
b2 = panel(ax, SEN, 0.0, b1 - 3.6)
ky = b2 - 0.5
items = [("o", INK, INK, "literal true"), ("o", "white", INK, "literal negated"), ("o", BLUE, "white", "gate drives line")]
xk = 0.0
for mk, fc, ec, lab in items:
    ax.plot(xk + 0.3, ky, mk, ms=4.2, mfc=fc, mec=ec, mew=0.9)
    ax.text(xk + 0.6, ky, lab, ha="left", va="center", fontsize=6.5, color=INK)
    xk += 1.4 + 0.33 * len(lab)
ax.plot([xk + 0.15, xk + 0.4, xk + 0.4, xk + 0.15], [ky + 0.3, ky + 0.3, ky - 0.3, ky - 0.3], color=CRIT, lw=1.3)
ax.text(xk + 0.6, ky, "⚠ conflict: both gates active, different lines", ha="left", va="center", fontsize=6.5, color=INK)
xk += 15.5
ax.plot([xk, xk + 0.45], [ky, ky], color=WARN_EDGE, lw=2.2, ls=(0, (1.5, 1)))
ax.text(xk + 0.6, ky, "hole", ha="left", va="center", fontsize=6.5, color=INK)
x1, y0, y1 = 43.0, ky - 0.6, 3.8
ax.set_xlim(-0.2, x1); ax.set_ylim(y0, y1); ax.set_aspect("equal")
fig.set_size_inches(7.16, 7.16 * (y1 - y0) / (x1 + 0.2))
fig.savefig("fig_pla.pdf"); fig.savefig("fig_pla.png", dpi=300)
