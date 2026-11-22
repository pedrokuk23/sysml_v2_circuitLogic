#!/usr/bin/env python3
"""OCRA baseline: contract-refinement checks with OCRA 2.1 (https://ocra.fbk.eu) on the case studies.

OCRA is not redistributed (FBK licence, no redistribution): download it and set OCRA=/path/to/ocra-linux64.

1. FireSat resolution flow-down (resFlow, resFlowRevised, geoFlow) in the angular, linear form used for the Pacti
   baseline: r = 30 m / h is the angular budget, MR-RES  X = h (beta + eps) <= 30  <=>  beta + eps <= r.  ORB-1
   (h <= 700 km) gives r >= 300/7 urad, ORB-GEO r = 30/35.786 urad, PAY-2 (D >= 0.26 m, beta = 2.44 lambda / D,
   lambda = 4.2 um) beta <= 10.248/0.26 urad, ADCS-1 eps <= 5 urad, ADCS-1R eps <= 3 urad. The bounds on r and beta
   are monotone in h and D and are written by hand, as for Pacti. The direct nonlinear encoding (X := h * (blur + eps),
   blur * D = const) did not terminate within 10 min.
2. Lockheed Martin mode logic, original and revised (generated from the compiler's IR, so the formulas are those of
   the SysML v2 model): the system contract FSM-001 (one-step) refined by an Autopilot component, whose guarantee is
   the conjunction of its requirements and glossary axioms, and a Sensor component, which assumes the port contract
   (mode or request) and guarantees its requirements. OCRA checks that the children refine FSM-001 and that the
   Sensor's assumption is met by the Autopilot (the 'correct environment' check).

    OCRA=... python3 baselines/ocra/ocra_baseline.py [OUTDIR]
"""
import json, os, re, subprocess, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from semantics import compile_model

OCRA = os.environ.get("OCRA", "ocra")

FIRESAT = {
    "resFlow":        ("ORB-1, PAY-2, ADCS-1",    "7 * v_r >= 300",    "v_eps <= 5"),
    "resFlowRevised": ("ORB-1, PAY-2, ADCS-1R",   "7 * v_r >= 300",    "v_eps <= 3"),
    "geoFlow":        ("ORB-GEO, PAY-2, ADCS-1R", "35.786 * v_r = 30", "v_eps <= 3"),
}


def firesat_oss(name):
    children, rcon, econ = FIRESAT[name]
    return f"""@requires discrete-time
-- FireSat {name}: MR-RES refined by {children}; angular form, microradians (see ocra_baseline.py)
COMPONENT FlowdownSystem system
INTERFACE
  OUTPUT PORT v_ok: boolean;
  CONTRACT parent
    assume: true;
    guarantee: always (v_ok);
REFINEMENT
  SUB payload: Payload;
  SUB adcs: Adcs;
  SUB orbit: Orbit;
  CONNECTION v_ok := payload.v_beta + adcs.v_eps <= orbit.v_r;
  CONTRACT parent REFINEDBY payload.c, adcs.c, orbit.c;
COMPONENT Payload
INTERFACE
  OUTPUT PORT v_beta: real;
  CONTRACT c
    assume: true;
    guarantee: always (v_beta >= 0 & 0.26 * v_beta <= 10.248);
COMPONENT Adcs
INTERFACE
  OUTPUT PORT v_eps: real;
  CONTRACT c
    assume: true;
    guarantee: always (v_eps >= 0 & {econ});
COMPONENT Orbit
INTERFACE
  OUTPUT PORT v_r: real;
  CONTRACT c
    assume: true;
    guarantee: always (v_r > 0 & {rcon});
"""


from z3 import (is_and, is_or, is_not, is_implies, is_eq, is_distinct, is_true, is_false, is_int_value, is_const,
                is_app_of, is_bool, Z3_OP_ITE)


def ox(e):
    """z3 formula of the compiler -> Othello (enumerations are integer ranges, as in the compiler's SMT encoding)."""
    if is_true(e): return "TRUE"
    if is_false(e): return "FALSE"
    if is_int_value(e): return str(e.as_long())
    if is_not(e): return f"(! {ox(e.arg(0))})"
    if is_and(e): return "(" + " & ".join(ox(c) for c in e.children()) + ")"
    if is_or(e): return "(" + " | ".join(ox(c) for c in e.children()) + ")"
    if is_implies(e): return f"({ox(e.arg(0))} -> {ox(e.arg(1))})"
    if is_eq(e): return f"({ox(e.arg(0))} {'<->' if is_bool(e.arg(0)) else '='} {ox(e.arg(1))})"
    if is_distinct(e): return f"({ox(e.arg(0))} != {ox(e.arg(1))})"
    if is_app_of(e, Z3_OP_ITE): return f"(case {ox(e.arg(0))} : {ox(e.arg(1))}; TRUE : {ox(e.arg(2))}; esac)"
    if is_const(e): return "v_" + str(e)
    raise ValueError(str(e))


def othello(e, enums):
    e = re.sub(r"(\w+)::(\w+)", lambda m: f"{m.group(1)}_{m.group(2)}", e)
    e = re.sub(r"\b(?:fromSensor|fromAp|toSensor|toAp|apSide|senSide)\.", "", e)
    e = e.replace("==", "=")
    e = re.sub(r"\bimplies\b", "->", e)
    e = re.sub(r"\band\b", "&", e)
    e = re.sub(r"\bor\b", "|", e)
    e = re.sub(r"\bnot\b", "!", e)
    lits = {f"{en}_{l}" for en, ls in enums.items() for l in ls}
    return re.sub(r"\b([A-Za-z_]\w*)\b", lambda m: m.group(1) if m.group(1) in lits else "v_" + m.group(1), e)


def lm_oss(model):
    S = compile_model(model)
    ir, R = S.ir, S.ir["requirements"]
    enums = ir["enums"]
    ty = {a["name"]: a["type"] for r in R.values() for a in r["attrs"]}
    # a requirement belongs to the autopilot if it mentions an ApState attribute or an autopilot input, else to the sensor
    ap_in = {"standby", "apfail", "supported"}
    def owner(r):
        names = {a["name"] for a in r["attrs"]}
        if any(ty[n] == "ApState" for n in names) or names & ap_in:
            return "Autopilot"
        return "Sensor"
    groups = {"Autopilot": [], "Sensor": []}
    for k, r in R.items():
        if re.search(r"\bpre\d+_", r["expr"]) or k.startswith("FSM-001"):
            continue
        groups[owner(r)].append(k)
    outs = {g: sorted({a["name"] for k in ks for a in R[k]["attrs"] if a["dir"] == "out"}) for g, ks in groups.items()}
    ins = {g: sorted({a["name"] for k in ks for a in R[k]["attrs"] if a["dir"] == "in"} - set(outs[g])) for g, ks in groups.items()}
    parent = R["FSM-001"]
    sys_out = sorted({a["name"] for a in parent["attrs"] if a["dir"] == "out"})
    produced = set(outs["Autopilot"]) | set(outs["Sensor"])
    sys_in = sorted((set(ins["Autopilot"]) | set(ins["Sensor"])) - produced)
    def typ(n):
        t = ty[n]
        return "boolean" if t == "Boolean" else f"0..{len(enums[t]) - 1}"
    port_contract = ox(S.E(next(iter(ir["asserts"].values()))))
    L = ["@requires discrete-time",
         f"-- {os.path.basename(model)}: FSM-001 (one-step) refined by the autopilot and sensor requirement sets;",
         "-- generated from the compiler's IR by baselines/ocra/ocra_baseline.py",
         "COMPONENT FSM system", "INTERFACE"]
    L += [f"  INPUT PORT v_{n}: {typ(n)};" for n in sys_in] + [f"  OUTPUT PORT v_{n}: {typ(n)};" for n in sys_out]
    L += ["  CONTRACT parent", "    assume: true;", f"    guarantee: always ({ox(S.R['FSM-001'])});",
          "REFINEMENT", "  SUB ap: Autopilot;", "  SUB sen: Sensor;"]
    for g, sub in (("Autopilot", "ap"), ("Sensor", "sen")):
        other = "sen" if sub == "ap" else "ap"
        other_g = "Sensor" if g == "Autopilot" else "Autopilot"
        for n in ins[g]:
            src = f"v_{n}" if n in sys_in else f"{other}.v_{n}"
            L.append(f"  CONNECTION {sub}.v_{n} := {src};")
    for n in sys_out:
        L.append(f"  CONNECTION v_{n} := {'ap' if n in outs['Autopilot'] else 'sen'}.v_{n};")
    L.append("  CONTRACT parent REFINEDBY ap.c, sen.c;")
    for g in ("Autopilot", "Sensor"):
        L += [f"COMPONENT {g}", "INTERFACE"] + [f"  INPUT PORT v_{n}: {typ(n)};" for n in ins[g]] + \
             [f"  OUTPUT PORT v_{n}: {typ(n)};" for n in outs[g]]
        g_expr = " & ".join(ox(S.R[k]) for k in groups[g])
        L += ["  CONTRACT c", f"    assume: {'always (' + port_contract + ')' if g == 'Sensor' else 'true'};",
              f"    guarantee: always ({g_expr});"]
    return "\n".join(L) + "\n", groups


def run(path):
    cmd = path[:-4] + ".cmd"
    open(cmd, "w").write(f"ocra_check_refinement -i {os.path.basename(path)}\nquit\n")
    t = time.time()
    p = subprocess.run([OCRA, "-ocra-discrete-time", "-source", os.path.basename(cmd)], cwd=os.path.dirname(path), capture_output=True,
                       text=True, timeout=900, stdin=subprocess.DEVNULL)
    out = p.stdout + p.stderr
    open(path[:-4] + ".log", "w").write(out)
    checks = {f"{a}:{b}": c for a, b, c in
              re.findall(r'Checking the correct (implementation|environment) of "([\w.]+)"\.\.\.(?:.*?)\[(OK|NOT OK|BOUND OK)', out, re.S)}
    return checks, round(time.time() - t, 2)


def main(out):
    os.makedirs(out, exist_ok=True)
    res = {}
    for name in FIRESAT:
        p = os.path.join(out, f"firesat_{name}.oss")
        open(p, "w").write(firesat_oss(name))
        res[f"firesat_{name}"] = dict(zip(("checks", "seconds"), run(p)))
    for m in ("lmcps_fsm", "lmcps_fsm_rev"):
        p = os.path.join(out, f"{m}.oss")
        text, groups = lm_oss(os.path.join(ROOT, "models", m + ".sysml"))
        open(p, "w").write(text)
        c, dt = run(p)
        res[m] = dict(checks=c, seconds=dt, autopilot=groups["Autopilot"], sensor=groups["Sensor"])
    for k, v in res.items():
        print(k, v["checks"], f"{v['seconds']} s")
    json.dump(res, open(os.path.join(out, "ocra_results.json"), "w"), indent=1)


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "results", "reference", "ocra"))
