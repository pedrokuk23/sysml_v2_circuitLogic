"""Feature-model baseline (flamapy, SAT): the FireSat variability as a UVL feature model.
(a) structure only: what a feature-model tool sees without the physics;
(b) with cross-tree constraints obtained by folding the physics and the allocation capacity into Boolean
    constraints (the configuration circuit of the compiler, exported as CNF)."""
import itertools, json, sys, time
import os
ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import And, BoolVal, IntVal, substitute, simplify, is_true
from sympy import symbols
from sympy.logic import POSform
from parser import parse
from semantics import Semantics, compile_model
import analysis

S = compile_model(os.path.join(ROOT, "models", "firesat.sysml"))
V = analysis.check_variability(S)
names = V["variations"]; U = list(names)
funs = [f for f in V["allocation_functions"] if f not in ("downlink",)]
R = dict(S.R)
from z3 import If, RealVal
acts = {n: a for ad in S.ir["actions"].values() for n, a in ad["attrs"].items()}
R["CAP"] = sum(If(S.onboard[f], RealVal(acts[f]["cpuLoad"]), RealVal(0)) for f in V["allocation_functions"]) <= S.variant_attr("bus", "cpuCapacity")
feat = [names[u][1] for u in U] + [f + "OnBoard" for f in funs]          # second variant = feature selected
ones = []
for bits in itertools.product([0, 1], repeat=len(feat)):
    sub = [(S.sel[u], IntVal(b)) for u, b in zip(U, bits[:len(U)])]
    sub += [(S.onboard[f], BoolVal(bool(b))) for f, b in zip(funs, bits[len(U):])] + [(S.onboard["downlink"], BoolVal(True))]
    if all(is_true(simplify(substitute(f, *sub))) for f in R.values()):
        ones.append(list(bits))
sy = symbols(" ".join(feat))
cnf = POSform(list(sy), ones)
def uvl(constraints):
    L = ["features", "    FireSat", "        mandatory"]
    for u in U:
        L += [f"            {u}", "                alternative", f"                    {names[u][0]}", f"                    {names[u][1]}"]
    L += ["        optional"] + [f"            {f}OnBoard" for f in funs]
    if constraints:
        L += ["constraints"]
        for cl in (cnf.args if cnf.func.__name__ == "And" else [cnf]):
            lits = cl.args if cl.func.__name__ == "Or" else [cl]
            L.append("    " + " | ".join(("!" + str(l.args[0])) if l.func.__name__ == "Not" else str(l) for l in lits))
    return "\n".join(L) + "\n"
open("firesat_structure.uvl", "w").write(uvl(False))
open("firesat_folded.uvl", "w").write(uvl(True))
from flamapy.metamodels.fm_metamodel.transformations import UVLReader
from flamapy.metamodels.pysat_metamodel.transformations import FmToPysat
from flamapy.metamodels.pysat_metamodel.operations import (PySATConfigurationsNumber, PySATDeadFeatures,
                                                            PySATCoreFeatures)
out = {}
for k in ("firesat_structure", "firesat_folded"):
    t = time.time()
    fm = UVLReader(f"{k}.uvl").transform()
    sat = FmToPysat(fm).transform()
    n = PySATConfigurationsNumber().execute(sat).get_result()
    dead = PySATDeadFeatures().execute(sat).get_result()
    core = PySATCoreFeatures().execute(sat).get_result()
    out[k] = dict(products=n, dead=sorted(map(str, dead)), core=sorted(map(str, core)), seconds=round(time.time() - t, 2))
out["cnf_clauses"] = str(cnf)
print(json.dumps(out, indent=1, default=str)); json.dump(out, open("flamapy_results.json", "w"), indent=1, default=str)
