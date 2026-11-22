#!/usr/bin/env python3
"""NASA Lift+Cruise (FRET case study, Pressburger et al., REFSQ 2023 and NASA/TM-20220017032) on the unrolled circuit.

The requirements are NASA's (fret/caseStudies/LiftPlusCruise, Apache-2.0); fret2sysml.py turns their past-time
semantics into the SysML v2 models models/third_party/lpc_{mini,full}.sysml. Each check below reproduces a result
that NASA reports:

  B1  without the stay requirements the mode logic lets the aircraft jump from wing-borne to thrust-borne;
  B2  the three formalizations of each stay requirement (_NEXT, _pre, _until) are equivalent;
  B3  thrust-borne is reached first at step 11: 'within 10 ticks' fails and 'within 11 ticks' holds (full set
      without wind); the mini set fails with 6 ticks and holds with 12;
  B4  with wind as an uncontrolled input (|w| <= 30, |dw| <= 10, w(0) = 10, kgs = kias + w): with kias >= 0 no trace
      reaches thrust-borne whatever the bound, while without kias >= 0 it does only with negative airspeed; with
      |w| <= 20 thrust-borne cannot be reached before step 13.

For the sets without inputs (NASA declares every variable an output, and the wind the only input), a lasso is an
infinite trace that meets every requirement, hence realizability; unrealizability is shown by a finite refutation, the
length of the shortest prefix that no trace meets (recorded as 'no_trace_of_steps'). With the wind input, the
check fixes one admissible wind sequence (the ramp 10, 20, 30, ... up to the bound): a requirement that no output
trace meets under that sequence is unrealizable; a requirement met under it is only not refuted.

    python3 experiments/third_party/lpc.py [OUT.json]
"""
import json, os, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import And, Or, RealVal
from semantics import compile_model
import unroll

SHOW = ["lift_mode", "kias", "kgs", "hover_control_mode", "wind_speed"]


def no_trace(S, keys, upto):
    """Smallest number of steps n <= upto such that no trace of n steps meets keys at every step (a BMC refutation)."""
    for n in range(upto + 1):
        if not unroll.trace(S, keys, n)[0]:
            return n + 1
    return None


def main(out):
    T0 = time.time()
    res = {}
    # ---------------------------------------------------------------- mini set
    S = compile_model(os.path.join(ROOT, "models", "third_party", "lpc_mini.sysml"))
    R = list(S.R)
    E = S.enums["LiftModeKind"]; TB, WB = E.index("thrust_borne"), E.index("wing_borne")
    reach = [k for k in R if "REACH" in k]
    base = [k for k in R if k not in reach]
    show = [n for n in SHOW if n in S.vars]
    t0 = time.time()
    trans = [k for k in base if "STAY_ON" not in k]
    ok, tr = unroll.trace(S, trans, 2, lambda U: And(U.var("lift_mode", 0) == WB, U.var("lift_mode", 1) == TB), show)
    ok2, _ = unroll.trace(S, base, 12, lambda U: Or(*[And(U.var("lift_mode", t) == WB, U.var("lift_mode", t + 1) == TB)
                                                     for t in range(12)]))
    res["B1_mini"] = dict(transitions_only_WB_to_TB=ok, example=tr, with_stay_requirements_WB_to_TB_within_12=ok2,
                          seconds=round(time.time() - t0, 1))
    t0 = time.time()
    t, tr = unroll.earliest(S, base, 20, lambda U, t: U.var("lift_mode", t) == TB, show)
    res["B3_mini_earliest_TB"] = dict(step=t, trace=tr, seconds=round(time.time() - t0, 1))
    for k in reach:
        t0 = time.time()
        ok, _ = unroll.lasso(S, base + [k], 20)
        res[f"B3_mini_{k}"] = dict(realizable=ok, no_trace_of_steps=None if ok else no_trace(S, base + [k], 24),
                                   seconds=round(time.time() - t0, 1))
    group = [k for k in base if not k.startswith("GLO") and ("_TO_" in k or "STAY_ON" in k)]
    t0 = time.time()
    res["mini_mode_logic"] = dict(
        requirements=group,
        reachable_conflicts_within_12=unroll.reachable_conflicts(S, base, group, 12),
        reachable_holes_within_12=[h["step"] for h in unroll.reachable_holes(S, base, group, 12)],
        seconds=round(time.time() - t0, 1))
    # ---------------------------------------------------------------- full set
    S = compile_model(os.path.join(ROOT, "models", "third_party", "lpc_full.sysml"))
    R = list(S.R); req = [k for k in R if not k.startswith("GLO")]
    glo = [k for k in R if k.startswith("GLO")]
    reach = [k for k in req if "REACH" in k]; wind = [k for k in req if "WIND" in k]
    E = S.enums["LiftModeKind"]; TB = E.index("thrust_borne")
    show = [n for n in SHOW if n in S.vars]
    t0 = time.time()
    N = next(n for n in range(0, 6) if not unroll.trace(S, R, n)[0])
    core = list(req)
    for k in list(core):
        trial = [x for x in core if x != k]
        if not unroll.trace(S, glo + trial, N)[0]:
            core = trial
    res["full_whole_file"] = dict(consistent=False, first_failing_prefix_steps=N + 1, minimal_conflict=core,
                                  seconds=round(time.time() - t0, 1))
    eqs = {}
    t0 = time.time()
    for fam in ("TB", "STB", "SWB", "WB"):
        v = [f"LPC_{fam}_STAY_ON_{x}" for x in ("NEXT", "pre", "until")]
        for a, b in ((v[0], v[1]), (v[1], v[2])):
            eqs[f"{a} = {b}"] = unroll.equivalent_over(S, a, b, 8, context=glo)[0]
    res["B2_full_stay_variants_equivalent_over_9_steps"] = dict(pairs=eqs, seconds=round(time.time() - t0, 1))
    nowind = [k for k in R if k not in reach and k not in wind]
    for k in reach:
        t0 = time.time()
        ok, _ = unroll.lasso(S, nowind + [k], 24)
        res[f"B3_full_nowind_{k}"] = dict(realizable=ok, no_trace_of_steps=None if ok else no_trace(S, nowind + [k], 24),
                                          seconds=round(time.time() - t0, 1))
    base = [k for k in R if "REACH" not in k and "WIND" not in k and k != "LPC_KIAS_KGS"]
    for B, kias0 in ((30, True), (30, False), (20, True)):
        keys = [k for k in base if kias0 or k != "LPC_KIAS_0"] + [
            "LPC_INIT_WIND_SPEED_assumption", "LPC_WIND_SPEED_DERIV_assumption", "LPC_KIAS_KGS_WIND_SPEED",
            f"LPC_WIND_SPEED_{B}_assumption"]
        adv = lambda U, B=B: And(*[U.var("wind_speed", t) == RealVal(min(10 + 10 * t, B)) for t in range(U.N + 1)])
        t0 = time.time()
        t, tr = unroll.earliest(S, keys, 20, lambda U, t: And(U.var("lift_mode", t) == TB, adv(U)), show)
        res[f"B4_wind_{B}_kias_nonneg_{kias0}"] = dict(earliest_TB_under_ramp_wind=t, last_step=tr[-1] if tr else None,
                                                       min_kias=min(float(eval(r["kias"])) for r in tr) if tr else None,
                                                       seconds=round(time.time() - t0, 1))
    res["total_seconds"] = round(time.time() - T0, 1)
    json.dump(res, open(out, "w"), indent=1, default=str)
    for k, v in res.items():
        if isinstance(v, dict):
            print(k, {a: b for a, b in v.items() if a not in ("trace", "example")})
    return res


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "results", "reference", "third_party", "lpc_results.json"))
