#!/usr/bin/env python3
"""Case 1: Lockheed Martin / NASA LMCPS 'Finite State Machine' requirements (FRET repository, RE 2020).

The public file keeps both the original requirements and the later revised versions (v2, weak). That version
history is a natural experiment: do the logic checks, run on the ORIGINAL set, point exactly at what the authors
later revised, and do they propose the same repair?
Then the parent FSM-001 (pullup) is checked against its children (deduction theorem), first in one step and
then over time (bounded exploration of the composed autopilot+sensor), for each of its three versions.
"""
import os
import json, itertools, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import Int, Bool, And, Or, Not, Implies, BoolVal, Exists
from logic_engine import finite_region, free_consts, conflicts, redundant, vacuous, coverage, valid, refines, is_sat, dead_parts

SRC = os.path.join(os.environ.get("FRET_DIR", os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "external", "fret")), "caseStudies", "LMCPS", "LM_requirements.json")
reqtext = {r["reqid"]: r["fulltext"].strip() for r in json.load(open(SRC))["requirements"]}

T, N, M, S = 0, 1, 2, 3                 # autopilot: transition, nominal, maneuver, standby (FRET numbering)
SN, ST, SF = 0, 1, 2                    # sensor: nominal, transition, fault
state, STATE, senstate, SENSTATE = Int("state"), Int("STATE"), Int("senstate"), Int("SENSTATE")
standby, apfail, supported, good = Bool("standby"), Bool("apfail"), Bool("supported"), Bool("good")
request, limits, activeMode, pullup = Bool("request"), Bool("limits"), Bool("activeMode"), Bool("pullup")
INPUTS = [state, senstate, standby, apfail, supported, good, request, limits, activeMode]
A = And(state >= 0, state <= 3, STATE >= 0, STATE <= 3, senstate >= 0, senstate <= 2, SENSTATE >= 0, SENSTATE <= 2)

R = {  # (formula, component); transcribed from the FRET 'fulltext' of each id
    "FSM-002":    (Implies(And(standby, state == T), STATE == S), "AP"),
    "FSM-003":    (Implies(And(state == T, good, supported), STATE == N), "AP"),
    "FSM-003v2":  (Implies(And(state == T, good, supported, Not(standby)), STATE == N), "AP"),
    "FSM-004":    (Implies(And(Not(good), state == N), STATE == M), "AP"),
    "FSM-004v2":  (Implies(And(state == N, Not(good), Not(standby)), STATE == M), "AP"),
    "FSM-005":    (Implies(And(state == N, standby), STATE == S), "AP"),
    "FSM-006":    (Implies(And(state == M, standby, good), STATE == S), "AP"),
    "FSM-007":    (Implies(And(state == M, supported, good), STATE == T), "AP"),
    "FSM-007v2":  (Implies(And(state == M, supported, good, Not(standby)), STATE == T), "AP"),
    "FSM-008v1":  (Implies(And(state == S, Not(standby)), STATE == T), "AP"),
    "FSM-008v2":  (Implies(And(state == S, Not(standby), Not(apfail)), STATE == T), "AP"),
    "FSM-009":    (Implies(And(state == S, apfail), STATE == M), "AP"),
    "FSM-010":    (Implies(And(senstate == SN, limits), SENSTATE == SF), "SEN"),
    "FSM-011v1":  (Implies(And(senstate == SN, Not(request)), SENSTATE == ST), "SEN"),
    "FSM-011v2":  (Implies(And(senstate == SN, Not(request), Not(limits)), SENSTATE == ST), "SEN"),
    "FSM-012":    (Implies(And(senstate == SF, Not(request), Not(limits)), SENSTATE == ST), "SEN"),
    "FSM_012_weak": (Implies(And(senstate == SF, Or(Not(request), Not(limits))), SENSTATE == ST), "SEN"),
    "FSM-013":    (Implies(And(senstate == ST, request, activeMode), SENSTATE == SN), "SEN"),
}
ORIGINAL = ["FSM-002", "FSM-003", "FSM-004", "FSM-005", "FSM-006", "FSM-007", "FSM-008v1", "FSM-009",
            "FSM-010", "FSM-011v1", "FSM-012", "FSM-013"]
REVISED_BY = {"FSM-003": "FSM-003v2", "FSM-004": "FSM-004v2", "FSM-007": "FSM-007v2",
              "FSM-008v1": "FSM-008v2", "FSM-011v1": "FSM-011v2"}


def ante(rid):
    return R[rid][0].arg(0)


def repair_candidates(a, b):
    """Resolve a clash between a and b by giving priority to one: the other's antecedent gets ¬(antecedent of the winner)."""
    out = {}
    for lose, win in ((a, b), (b, a)):
        f = R[lose][0]
        out[f"{lose} yields to {win}"] = Implies(And(f.arg(0), Not(ante(win))), f.arg(1))
    return out


def equivalent(f, g):
    return valid(f == g, A)[0]


def main():
    res = {}
    orig = {k: R[k][0] for k in ORIGINAL}
    # 1. conflicts in the original set
    C = conflicts(orig, A, INPUTS, max_size=3)
    ENUM = {state: {0: "T", 1: "N", 2: "M", 3: "S"}, senstate: {0: "N", 1: "T", 2: "F"}}
    for c in C:
        fs = [orig[k] for k in c["requirements"]]
        comp = R[c["requirements"][0]][1]
        outs = [STATE, SENSTATE]
        bools = [b for b in (standby, apfail, supported, good, request, limits, activeMode)
                 if any(str(b) in str(f) for f in fs)]
        en = {state: ENUM[state]} if comp == "AP" else {senstate: ENUM[senstate]}
        c["region"] = finite_region(And(state >= 0, state <= 3, senstate >= 0, senstate <= 2, Not(Exists(outs, And(A, *fs)))), bools, en)
    res["conflicts_original"] = C
    # 2. repairs and comparison with the authors' revisions
    rep = []
    for c in C:
        a, b = c["requirements"]
        cands = repair_candidates(a, b)
        match = []
        for name, f in cands.items():
            for old, new in REVISED_BY.items():
                if old in (a, b) and equivalent(f, R[new][0]):
                    match.append(dict(candidate=name, equals=new))
        rep.append(dict(pair=[a, b], candidates={k: str(v) for k, v in cands.items()}, matches_history=match))
    res["repairs"] = rep
    flagged = {r for c in C for r in c["requirements"]}
    revised = set(REVISED_BY)
    res["history_recall"] = dict(revised_by_authors=sorted(revised), revised_and_flagged=sorted(revised & flagged),
                                 flagged_not_revised=sorted(flagged - revised),
                                 repairs_matching_history=sum(1 for r in rep if r["matches_history"]))
    # 3. the revised set
    rev = {REVISED_BY.get(k, k): R[REVISED_BY.get(k, k)][0] for k in ORIGINAL}
    res["conflicts_revised"] = conflicts(rev, A, INPUTS, max_size=3)
    res["redundant_revised"] = redundant(rev, A)
    res["vacuous_revised"] = vacuous(rev, A)
    # 4. coverage of each source state (holes = situations where no requirement says what happens)
    cov = {}
    for comp, var, states, names in (("AP", state, (T, N, M, S), "TNMS"), ("SEN", senstate, (SN, ST, SF), "NTF")):
        for s, nm in zip(states, names):
            cases = {k: ante(k) for k in rev if R[k][1] == comp and is_sat(ante(k), var == s)[0]}
            cv = coverage(cases, And(var == s), INPUTS) if cases else dict(complete=False, hole_region=f"{var}=={s}")
            bools = [standby, apfail, supported, good] if comp == "AP" else [request, limits, activeMode]
            hole = And(var == s, Not(Or(*cases.values()))) if cases else (var == s)
            n_hole = sum(1 for bits in itertools.product([0, 1], repeat=len(bools))
                         if is_sat(hole, *[b if x else Not(b) for b, x in zip(bools, bits)])[0])
            cov[f"{comp}:{nm}"] = dict(cases=list(cases), complete=cv["complete"], n_situations=2 ** len(bools),
                                       n_holes=n_hole, hole=finite_region(hole, bools, {}),
                                       overlaps=cv.get("overlaps", []))
    res["coverage_revised"] = cov
    # 5. the 'weak' variant of FSM-012 against the original
    res["FSM-012_vs_weak"] = dict(weak_implies_original=valid(Implies(R["FSM_012_weak"][0], R["FSM-012"][0]), A)[0],
                                  original_implies_weak=valid(Implies(R["FSM-012"][0], R["FSM_012_weak"][0]), A)[0])
    # 6. parent FSM-001v1 against all children in one step
    autopilot = And(Not(standby), supported, Not(apfail))
    p1 = Implies(And(limits, autopilot), pullup)
    res["FSM-001v1_one_step"] = refines(p1, list(rev.values()), A)
    res["pullup_mentioned_by_children"] = any("pullup" in str(f) for f in rev.values())
    json.dump(res, open(os.path.join(os.environ.get("OUT", "."), "case_lmcps_fsm.json"), "w"), indent=1, ensure_ascii=False)
    return res


if __name__ == "__main__":
    r = main()
    print(json.dumps(r, indent=1, ensure_ascii=False)[:6000])
