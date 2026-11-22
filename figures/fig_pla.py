"""Requirements of the Lockheed Martin state machines drawn as programmable-logic arrays (PLA).

Each row is one requirement (an AND gate). Columns on the left are input literals: a filled dot means the literal
appears true in the antecedent, an open circle means it appears negated. Columns on the right are the lines of the
next-state bus: a dot shows which line the gate drives. Conflicts (bus contention) are bracketed in red with an
icon and a label; holes (undriven situations) are listed under each panel. Text is always black."""
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import FancyBboxPatch

INK, INK2, GRID = "#0b0b0b", "#52514e", "#b9b8b3"
BLUE = "#2a78d6"            # driven values
CRIT = "#d03b3b"            # conflicts (always with a symbol and a label)
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


FS = 8.0          # every text at 8 pt or more at print size (figure is drawn at the text width, 4.48 in)


def panel(ax, M, x0=0.0, ytop=0.0):
    ni, no, nr = len(M["inputs"]), len(M["outputs"]), len(M["rows"])
    dx, dy = 1.0, 1.0
    xin = [x0 + 3.6 + k * dx for k in range(ni)]
    xg = xin[-1] + 1.3
    xout = [xg + 1.4 + k * dx for k in range(no)]
    yrow = [ytop - 1.0 - r * dy for r in range(nr)]
    ybot = yrow[-1] - 0.6
    ax.text(x0, ytop + 4.3, M["title"], ha="left", va="bottom", fontsize=FS + 1, fontweight="bold", color=INK)
    for x, n in zip(xin, M["inputs"]):
        ax.text(x, ytop + 0.2, n, rotation=60, ha="left", va="bottom", fontsize=FS, color=INK)
        ax.plot([x, x], [ytop, ybot], color=GRID, lw=0.6, zorder=1)
    for x, n in zip(xout, M["outputs"]):
        ax.text(x, ytop + 0.2, f"next={n}", rotation=60, ha="left", va="bottom", fontsize=FS, color=INK)
        ax.plot([x, x], [ytop, ybot], color=BLUE, lw=0.8, alpha=0.45, zorder=1)
    for (name, lits, out), y in zip(M["rows"], yrow):
        ax.text(x0 + 3.2, y, name, ha="right", va="center", fontsize=FS, color=INK)
        ax.plot([xin[0] - 0.3, xg - 0.36], [y, y], color=INK2, lw=0.6, zorder=1)
        for x, n in zip(xin, M["inputs"]):
            if n in lits:
                if lits[n]:
                    ax.plot(x, y, "o", ms=4.6, color=INK, zorder=3)
                else:
                    ax.plot(x, y, "o", ms=4.6, mfc="white", mec=INK, mew=0.9, zorder=3)
        ax.add_patch(FancyBboxPatch((xg - 0.4, y - 0.42), 0.8, 0.84, boxstyle="round,pad=0.0,rounding_size=0.15",
                                    fc="white", ec=INK, lw=0.8, zorder=3))
        ax.text(xg, y, "&", ha="center", va="center", fontsize=FS, fontweight="bold", color=INK, zorder=4)
        xo = xout[M["outputs"].index(out)]
        ax.plot([xg + 0.4, xo], [y, y], color=BLUE, lw=1.2, zorder=2)
        ax.plot(xo, y, "s", ms=4.6, color=BLUE, mec="white", mew=0.8, zorder=3)
    xb = xout[-1] + 0.7
    for i, j, tag, region in M["conflicts"]:
        y1, y2 = yrow[i], yrow[j]
        ax.plot([xb, xb + 0.3, xb + 0.3, xb], [y1, y1, y2, y2], color=CRIT, lw=1.6, zorder=2)
        ax.text(xb + 0.55, (y1 + y2) / 2, f"\u26a0 {tag}", ha="left", va="center", fontsize=FS, color=INK)
    yh = ybot - 0.35
    for k, (i, j, tag, region) in enumerate(M["conflicts"]):
        ax.text(x0, yh - 1.0 * k, f"\u26a0 {tag}, {M['rows'][i][0]}/{M['rows'][j][0][4:]}: {region}", ha="left",
                va="top", fontsize=FS, color=INK)
    yh = yh - 1.0 * len(M["conflicts"]) - 0.3
    for k, (st, frac, cond) in enumerate(M["holes"]):
        yy = yh - 1.0 * k
        ax.text(x0, yy, f"hole in {st}, {frac}: {cond}", ha="left", va="top", fontsize=FS, color=INK)
    return yh - 1.0 * len(M["holes"])


def short(M):
    M = dict(M)
    M["conflicts"] = [(i, j, t, r) for i, j, t, r in M["conflicts"]]
    return M


fig = plt.figure(figsize=(4.48, 6.0))
ax = fig.add_axes([0, 0, 1, 1]); ax.set_axis_off()
b1 = panel(ax, short(AP), 0.0, 0.0)
b2 = panel(ax, short(SEN), 0.0, b1 - 5.2)
ky2 = b2 + 0.3
x1, y0, y1 = 25.6, ky2 - 0.7, 5.6
ax.set_xlim(-0.2, x1); ax.set_ylim(y0, y1); ax.set_aspect("equal")
fig.set_size_inches(4.48, 4.48 * (y1 - y0) / (x1 + 0.2))
fig.savefig("fig_pla.pdf"); fig.savefig("fig_pla.png", dpi=200)
