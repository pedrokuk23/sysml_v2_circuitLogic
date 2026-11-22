#!/usr/bin/env python3
"""Can the environment force each conflict of the Lockheed Martin requirement set, whatever the system does?

The composed autopilot and sensor are played as a safety game on the twelve composite states (apState, senState).
In each step the environment chooses the inputs (standby, supported, apfail, limits) and the system chooses the next
states (nextState, nextSenState); a move is compliant when it satisfies the glossary axioms and the transition
requirements FSM-002 .. FSM-013 (FSM-001 is a property, not a constraint on moves). Signals that one machine reads
from the other (good, mode, request) follow from the states through the glossary.

To attribute a dead end to one conflicting pair, the other four pairs are repaired by one of their two priority
repairs (Proposition 2), in all 2^4 combinations. For each combination, the target is the set of situations (state,
inputs) in which no move is compliant, and the environment attractor of the target is computed by the usual fixpoint:
a state is in the attractor if some input leads into the target, or if some input leaves the system only moves into
the attractor. If the initial state is in the attractor for every combination, the conflict is forced against every
controller that satisfies the requirements, and the set is unrealizable because of that pair alone.

    python3 experiments/forced_conflicts.py [model.sysml] [OUT.json]
"""
import itertools, json, os, sys
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import Solver, And, Or, Not, Implies, BoolVal, sat
from semantics import compile_model
import analysis

INPUTS = ["standby", "supported", "apfail", "limits"]


def main(model, out):
    S = compile_model(model)
    ap, sen = S.enums["ApState"], S.enums["SenState"]
    glo = [f for k, f in S.R.items() if k.startswith("GLO")]
    trans = [k for k in S.R if k.startswith("FSM-0") and "v" not in k and k >= "FSM-002"]
    V = S.vars
    states = [(a, b) for a in range(len(ap)) for b in range(len(sen))]
    inputs = list(itertools.product((False, True), repeat=len(INPUTS)))
    init = (ap.index(S.ir["machines"]["apMachine"]["init"]), sen.index(S.ir["machines"]["senMachine"]["init"]))
    M = analysis.check_machines(S)
    pairs = [tuple(c["requirements"]) for v in M.values() for c in v["contention"]]
    name = lambda st: f"{ap[st[0]]}/{sen[st[1]]}"

    def repair(i, j):          # R_i yields to R_j
        return Implies(And(S.R[i].arg(0), Not(S.R[j].arg(0))), S.R[i].arg(1))

    def moves(reqs):
        mv = {}
        for st in states:
            for inp in inputs:
                s = Solver()
                s.add(S.domain, *glo, *reqs, V["apState"] == st[0], V["senState"] == st[1],
                      *[V[n] == BoolVal(v) for n, v in zip(INPUTS, inp)])
                ok = []
                while s.check() == sat:
                    m = s.model()
                    nx = (m.eval(V["nextState"], model_completion=True).as_long(),
                          m.eval(V["nextSenState"], model_completion=True).as_long())
                    ok.append(nx)
                    s.add(Or(V["nextState"] != nx[0], V["nextSenState"] != nx[1]))
                mv[st, inp] = ok
        return mv

    def attractor(mv):
        attr, depth, k = set(), {}, 0
        while True:
            new = set()
            for st in states:
                if st in attr:
                    continue
                for inp in inputs:
                    if not mv[st, inp] or all(nx in attr for nx in mv[st, inp]):
                        new.add(st); break
            if not new:
                return attr, depth
            for st in new:
                depth[st] = k
            attr |= new; k += 1

    res = {}
    for p in pairs:
        others = [q for q in pairs if q != p]
        runs = []
        for choice in itertools.product((0, 1), repeat=len(others)):
            rep = {}
            for (i, j), c in zip(others, choice):
                lo, hi = (i, j) if c == 0 else (j, i)
                rep[lo] = repair(lo, hi)
            reqs = [rep.get(k, S.R[k]) for k in trans]
            attr, depth = attractor(moves(reqs))
            runs.append(dict(repairs={k: "yields" for k in rep}, forced=init in attr, steps=depth.get(init),
                             attractor=sorted(name(s) for s in attr)))
        res[" / ".join(p)] = dict(forced_in_every_repair_of_the_others=all(r["forced"] for r in runs),
                                  max_steps_from_initial=max((r["steps"] for r in runs if r["forced"]), default=None),
                                  runs=len(runs), detail=runs)
    # control: with every pair repaired (2^5 choices), no situation lacks a compliant move
    ctrl = []
    for choice in itertools.product((0, 1), repeat=len(pairs)):
        rep_ = {}
        for (i, j), c in zip(pairs, choice):
            lo, hi = (i, j) if c == 0 else (j, i)
            rep_[lo] = repair(lo, hi)
        mv = moves([rep_.get(k, S.R[k]) for k in trans])
        ctrl.append(dict(dead_ends=sum(1 for v in mv.values() if not v), forced=init in attractor(mv)[0]))
    rep = dict(model=os.path.relpath(model, ROOT), initial=name(init), pairs=res,
               control_all_pairs_repaired=dict(combinations=len(ctrl), with_dead_end=sum(c["dead_ends"] > 0 for c in ctrl),
                                               forced=sum(c["forced"] for c in ctrl)))
    json.dump(rep, open(out, "w"), indent=1)
    print(json.dumps({k: {a: b for a, b in v.items() if a != "detail"} for k, v in res.items()}, indent=1))
    print("control:", rep["control_all_pairs_repaired"])


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0] if a else os.path.join(ROOT, "models", "lmcps_fsm.sysml"),
         a[1] if len(a) > 1 else os.path.join(ROOT, "results", "reference", "case_studies", "forced_conflicts.json"))
