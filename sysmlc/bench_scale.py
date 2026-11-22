#!/usr/bin/env python3
"""Scalability sweep on synthetic SysML v2 models (one state machine, S states, B Boolean inputs, R requirements
'state = q and l1 and l2 implies nextState = q2'). Compares the generic quantified conflict check (eq. 3) with the
circuit reading (Proposition 1: contention = two AND gates active together driving different bus lines, a
quantifier-free overlap test), and measures holes, AIG synthesis and the Yosys k-induction proof of all
requirements at once against the generated design.  Output: bench_scale.json"""
import tempfile, os
import itertools, json, os, random, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import And, Not, Or
from parser import parse
from semantics import Semantics
import analysis, verilog
from logic_engine import conflicts, is_sat


def generate(path, S, B, R, seed):
    rnd = random.Random(seed)
    st = [f"Q{i}" for i in range(S)]
    ins = [f"b{i}" for i in range(B)]
    L = ["package Synth {", "  private import ScalarValues::*;", f"  enum def St {{ {' '.join('enum ' + s + ';' for s in st)} }}"]
    trans = []
    for r in range(R):
        q, q2 = rnd.choice(st), rnd.choice(st)
        lits = rnd.sample(ins, 2)
        lit = [(x if rnd.random() < 0.5 else f"not {x}") for x in lits]
        L.append(f"  requirement def <'R-{r:03d}'> Req{r} {{ in attribute state : St; " +
                 " ".join(f"in attribute {x} : Boolean;" for x in lits) + " out attribute nextState : St;")
        L.append(f"    require constraint {{ (state == St::{q} and {lit[0]} and {lit[1]}) implies nextState == St::{q2} }} }}")
        trans.append((q, f"{lit[0]} and {lit[1]}", q2))
    L.append("  part def Sys { " + " ".join(f"in attribute {x} : Boolean;" for x in ins) + " exhibit state m { entry; then Q0; " +
             " ".join(f"state {s};" for s in st) + " " +
             " ".join(f"transition t{i} first {a} if {g} then {b};" for i, (a, g, b) in enumerate(trans)) + " } }")
    L.append("}")
    open(path, "w").write("\n".join(L) + "\n")


def run(S, B, R, seed=1, outdir=os.path.join(tempfile.gettempdir(), "sysmlc_bench")):
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, f"synth_{S}_{B}_{R}.sysml")
    generate(path, S, B, R, seed)
    t = {}
    t0 = time.time(); Sm = Semantics(parse(path)); g = analysis.machine_groups(Sm)["m"]; t["parse_s"] = time.time() - t0
    reqs = g["reqs"]; cur, nxt = g["cur"], g["nxt"]
    # circuit reading: pairwise antecedent overlap with different targets (quantifier-free)
    t0 = time.time(); circ = []
    keys = list(reqs)
    for a, b in itertools.combinations(keys, 2):
        if analysis.target(reqs[a]) != analysis.target(reqs[b]) and is_sat(Sm.domain, reqs[a].arg(0), reqs[b].arg(0))[0]:
            circ.append((a, b))
    t["conflicts_circuit_s"] = time.time() - t0; t["n_conflicts"] = len(circ)
    # generic quantified check (eq. 3), pairs only, capped by time
    if R <= 100:
        ins = [Sm.vars[n] for n in Sm.vars if Sm.vtype.get(n) == "Boolean"]
        t0 = time.time(); gen = conflicts(reqs, Sm.domain, [cur] + ins, max_size=2)
        t["conflicts_generic_s"] = time.time() - t0
        t["agree"] = sorted(map(tuple, (c["requirements"] for c in gen))) == sorted(circ)
    # holes
    t0 = time.time()
    nh = 0
    for i in range(S):
        antes = [f.arg(0) for f in reqs.values() if is_sat(f.arg(0), cur == i)[0]]
        nh += 0 if not is_sat(cur == i, Not(Or(*antes)) if antes else True)[0] else 1
    t["holes_s"] = time.time() - t0; t["states_with_holes"] = nh
    # EDA: emit design, prove all requirements at once by temporal induction, AIG sizes
    od = os.path.join(outdir, f"eda_{S}_{B}_{R}"); os.makedirs(od, exist_ok=True)
    verilog.emit_design(Sm, od)
    src = open(os.path.join(od, "design.sv")).read().replace("`ifdef P_", "`ifdef ALL_P_").replace("`ifdef ALL_P_", "`ifndef NONE_")
    open(os.path.join(od, "design_all.sv"), "w").write(src)
    t0 = time.time()
    log = verilog.run_yosys("read_verilog -formal design_all.sv; prep -top design; chformal -lower; select -assert-min 1 t:$assert; "
                            "sat -tempinduct -prove-asserts -maxsteps 10", od, timeout=1200)
    t["yosys_all_s"] = time.time() - t0
    t["yosys_all"] = "proved" if "SUCCESS" in log else ("counterexample" if "FAIL" in log else "error/timeout")
    t0 = time.time(); a = verilog.aig_stats("reqs.v", "reqs", od); t["aig_s"] = time.time() - t0
    t["aig_as_written_AND"] = a["as_written"]["AND"]; t["aig_optimized_AND"] = a["optimized"]["AND"]
    return dict(S=S, B=B, R=R, **t)


if __name__ == "__main__":
    out = []
    for S, B, R in [(8, 8, 10), (8, 8, 25), (8, 8, 50), (16, 10, 100), (16, 10, 200), (32, 12, 400)]:
        r = run(S, B, R); out.append(r); print(r, flush=True)
        json.dump(out, open(os.path.join(os.environ.get("OUT", "."), "bench_scale.json"), "w"), indent=1)
