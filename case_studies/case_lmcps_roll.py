#!/usr/bin/env python3
"""Case 2: real-valued requirements from the same LMCPS set (roll-hold reference AP-003A..D and the triplex
signal monitor TSM-002/003). Checks over linear real arithmetic: sub-formulas that are always true (simplification
by equivalence), case coverage and overlaps, conflicts with the input region where no output value satisfies them,
and the repair obtained by abduction."""
import os
import json, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import Real, Int, Bool, And, Or, Not, Implies, If, BoolVal, Exists
from logic_engine import dead_parts, coverage, conflicts, abduce, is_sat, qe, valid

roll, TK, ref = Real("roll_angle"), Real("TurnKnob"), Real("roll_hold_reference")
sign = If(roll >= 0, 1, -1)
absr = If(roll >= 0, roll, -roll)

# conditions exactly as in RollAutopilotSpec.lus (FRET export of AP-003A..D)
Cb = And(roll > -6.0, roll < 6.0)
Cc = absr >= 30.0
Cd = And(Or(TK >= 3.0, TK <= -3.0), Or(TK <= 30.0, TK >= -30.0))
Ca = Not(Or(Cb, Cc, Cd))
REQ = {"AP-003A": Implies(Ca, ref == roll), "AP-003B": Implies(Cb, ref == 0),
       "AP-003C": Implies(Cc, ref == 30 * sign), "AP-003D": Implies(Cd, ref == TK)}
res = {}
# 1. dead sub-formulas (equivalences): which parts of each requirement are always true / always false
res["dead_parts"] = {k: dead_parts(f) for k, f in REQ.items()}
# 2. conflicts: input situations (roll, TurnKnob) where no reference value satisfies two requirements
res["conflicts"] = conflicts(REQ, BoolVal(True), [roll, TK], max_size=2)
# 3. the probable intent: |TK| between 3 and 30 (and instead of or); still conflicting?
Cd2 = And(Or(TK >= 3.0, TK <= -3.0), And(TK <= 30.0, TK >= -30.0))
REQ2 = dict(REQ, **{"AP-003D'": Implies(Cd2, ref == TK)}); del REQ2["AP-003D"]
REQ2["AP-003A"] = Implies(Not(Or(Cb, Cc, Cd2)), ref == roll)
res["conflicts_with_and"] = conflicts(REQ2, BoolVal(True), [roll, TK], max_size=2)
# 4. coverage of the case split (as written)
res["coverage"] = coverage({"A": Ca, "B": Cb, "C": Cc, "D": Cd})
# 5. abduction: weakest condition on the inputs under which B and D can be kept together (= where they agree)
ab = abduce(BoolVal(False), [REQ["AP-003B"], REQ["AP-003D"]], BoolVal(True), [roll, TK])
res["B_D_compatible_region"] = str(qe(Exists([ref], And(REQ["AP-003B"], REQ["AP-003D"]))))

# ---- triplex signal monitor: fault-code cases for the selected value
FC, nofail = Int("FC"), Bool("no_fail")
cases = {"TSM-002 (no_fail)": nofail, "TSM-003a (FC=1)": FC == 1, "TSM-003b (FC=2)": FC == 2, "TSM-003c (FC=4)": FC == 4}
dom = And(FC >= 0, FC <= 7)
res["tsm_coverage"] = coverage(cases, dom)
res["tsm_coverage_with_glossary"] = coverage(cases, And(dom, nofail == (FC == 0), Or(FC == 0, FC == 1, FC == 2, FC == 4)))
json.dump(res, open(os.path.join(os.environ.get("OUT", "."), "case_lmcps_roll.json"), "w"), indent=1, ensure_ascii=False, default=str)
print(json.dumps(res, indent=1, ensure_ascii=False, default=str))
