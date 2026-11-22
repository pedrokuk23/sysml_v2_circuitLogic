#!/usr/bin/env python3
"""Case 1c (abduction over the holes): which unspecified situations must be completed with 'stay' for FSM-001v3
to follow (with the glossary axiom and FSM-012weak)? Greedy deletion gives a minimal set (each one is necessary);
these are the derived requirements the parent silently depends on."""
import os
import itertools, json, time
import case_lmcps_fsm_temporal as C

C.WEAK[0] = True
STAY = set()
orig_ap, orig_sen = C.ap_moves, C.sen_moves


def ap_moves(q, sb, af, su, g, policy):
    r = orig_ap(q, sb, af, su, g, "stay")
    hole = r == [q] and orig_ap(q, sb, af, su, g, "free") == [C.T, C.N, C.M, C.S]
    if hole and ("AP", q, sb, af, su, g) not in STAY:
        return [C.T, C.N, C.M, C.S]
    return r


def sen_moves(q, mode, req, lim, policy):
    r = orig_sen(q, mode, req, lim, "stay")
    hole = orig_sen(q, mode, req, lim, "free") == [C.SN, C.ST, C.SF]
    if hole and ("SEN", q, mode, req, lim) not in STAY:
        return [C.SN, C.ST, C.SF]
    return r


C.ap_moves, C.sen_moves = ap_moves, sen_moves
holes = []
for q in (C.T, C.N, C.M, C.S):
    for sb, af, su, g in itertools.product([False, True], repeat=4):
        if orig_ap(q, sb, af, su, g, "free") == [C.T, C.N, C.M, C.S]:
            holes.append(("AP", q, sb, af, su, g))
for q in (C.SN, C.ST, C.SF):
    for mode, req, lim in itertools.product([False, True], repeat=3):
        if orig_sen(q, mode, req, lim, "free") == [C.SN, C.ST, C.SF]:
            holes.append(("SEN", q, mode, req, lim))
STAY |= set(holes)
t0 = time.time()
assert C.explore("x", True)["holds"]["v3"]
needed = []
for h in holes:
    STAY.discard(h)
    if not C.explore("x", True)["holds"]["v3"]:
        STAY.add(h); needed.append(h)
print(len(holes), "holes;", len(needed), "needed;", round(time.time() - t0), "s")
for h in needed:
    print(h)
json.dump(dict(n_holes=len(holes), needed=[list(map(str, h)) for h in needed]),
          open(os.path.join(os.environ.get("OUT", "."), "case_lmcps_fsm_holes.json"), "w"), indent=1)
