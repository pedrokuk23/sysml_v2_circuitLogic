#!/usr/bin/env python3
"""Case 3 (revised physics): FireSat quantitative flow-down.

Parents (FireSat top-level mission requirements, CC0 gist by capsulecorplab after SMAD):
  MR-RES  30 m resolution (nadir)     MR-LOC  500 m location accuracy
Physics (first order, nadir):
  X = h (2.44 lambda / D + eps)       diffraction-limited spot diameter + line-of-sight JITTER during integration
  L = h theta_k + dr                  attitude-KNOWLEDGE error projected on ground + orbit position error
Children: an ILLUSTRATIVE allocation written by us, in which the jitter allocation (5 urad) misses the budget.
Operations: deduction (valid / counterexample), worst case, abduction by REPLACEMENT of one child, Craig interpolants
(payload / attitude-control interface and its margin), discretisation into Boolean lemmas, and the GEO revival bounds.
"""
import os
import itertools, json, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import Real, And, Or, Not, Implies, Q, ForAll
from logic_engine import refines, abduce, interpolate, is_sat, qe

h, D, eps, X = Real("h"), Real("D"), Real("eps"), Real("X")
thk, dr, L = Real("theta_k"), Real("dr"), Real("L")
K = Q(10248, 10**9)                       # 2.44 * 4.2e-6 m
PHYS = And(X == h * K / D + h * eps, L == h * thk + dr, D > 0, h > 0, eps >= 0, thk >= 0, dr >= 0)
PARENT = {"MR-RES": X <= 30, "MR-LOC": L <= 500}
CHILD = {
    "ORB-1":  And(h >= 500e3, h <= 700e3),
    "PAY-2":  D >= Q(13, 50),             # aperture >= 0.26 m
    "ADCS-1": eps <= Q(5, 10**6),         # jitter <= 5 urad
    "ADCS-2": thk <= Q(5236, 10**7),      # attitude knowledge <= 0.03 deg
    "NAV-1":  dr <= 100,
}


def worst(expr, hyp, lo=0.0, hi=1e5):
    for _ in range(70):
        mid = (lo + hi) / 2
        if is_sat(hyp, expr > mid)[0]:
            lo = mid
        else:
            hi = mid
    return round(hi, 3)


res = {}
for p, f in PARENT.items():
    r = refines(f, list(CHILD.values()), PHYS)
    r["worst_case"] = worst(X if p == "MR-RES" else L, And(PHYS, *CHILD.values()))
    res[p] = r; print(p, r["valid"], r["worst_case"], flush=True)

XR = h * K / D + h * eps
RES = XR <= 30
DOM = And(D > 0, h > 0, eps >= 0)
RC = {k: CHILD[k] for k in ("ORB-1", "PAY-2", "ADCS-1")}
ab = {}
for var, drop in ((eps, "ADCS-1"), (D, "PAY-2"), (h, "ORB-1")):
    kids = [f for k, f in RC.items() if k != drop]            # abduction by replacement: the child is removed
    a = abduce(RES, kids, DOM, [var])
    ab[f"replace {drop} (over {var})"] = str(a["W"]); print(drop, a["W"], flush=True)
a2 = abduce(RES, [RC["ORB-1"]], DOM, [D, eps])
ab["trade D x eps"] = str(a2["W"]); print("trade", a2["W"], flush=True)
res["abduction"] = ab

REPR = [RC["ORB-1"], RC["PAY-2"], eps <= Q(3, 10**6)]
res["MR-RES_repaired"] = refines(RES, REPR, DOM)
res["MR-RES_repaired"]["worst_case"] = worst(XR, And(DOM, *REPR))
print("repaired", res["MR-RES_repaired"]["valid"], res["MR-RES_repaired"]["worst_case"], flush=True)

# interface: u = 1/h, g = 1/D make the budget linear; shared variable beta = 2.44 lambda / D (diffraction blur)
u, g, beta = Real("u"), Real("g"), Real("beta_dif")
payload = And(beta == K * g, g > 0, g <= Q(50, 13))
adcs = And(eps >= 0, eps <= Q(3, 10**6), u >= Q(1, 700000), u <= Q(1, 500000), beta + eps > 30 * u)
I = interpolate(payload, adcs, [beta])
res["interface"] = dict(strongest=str(I["strongest"]), weakest=str(I["weakest"]),
                        payload_guarantees_urad=float(10.248e-6 / 0.26 * 1e6),
                        acs_tolerates_urad=(30 / 700e3 - 3e-6) * 1e6)
res["interface"]["margin_urad"] = res["interface"]["acs_tolerates_urad"] - res["interface"]["payload_guarantees_urad"]
print(res["interface"], flush=True)

# discretisation
atoms = {"a_h": h <= 700e3, "a_D": D >= Q(13, 50), "a_e3": eps <= Q(3, 10**6), "a_e5": eps <= Q(5, 10**6), "a_X": X <= 30}
base = And(PHYS, h >= 500e3)
feasible = []
for bits in itertools.product([0, 1], repeat=len(atoms)):
    if is_sat(base, *[f if b else Not(f) for f, b in zip(atoms.values(), bits)])[0]:
        feasible.append(list(bits))
from sympy import symbols
from sympy.logic import POSform
cnf = POSform(list(symbols(" ".join(atoms))), feasible)
res["discretisation"] = dict(feasible=len(feasible), of=32, lemmas=str(cnf))

# GEO revival bounds (abduction over the free aperture with the allocated jitter, and the two limit cases)
hg = 35786e3
Dg = Real("D_geo")
W = qe(ForAll([h], Implies(h == hg, h * (K / Dg + Q(3, 10**6)) <= 30)))
res["geo"] = dict(free_aperture_with_jitter_3urad=str(W), possible=is_sat(W, Dg > 0)[0],
                  D_min_m_with_zero_jitter=10.248e-6 * hg / 30, eps_max_urad_with_infinite_aperture=30 / hg * 1e6,
                  jitter_term_m=hg * 3e-6)
print(res["geo"], flush=True)
json.dump(res, open(os.path.join(os.environ.get("OUT", "."), "case_firesat2.json"), "w"), indent=1, default=str)
