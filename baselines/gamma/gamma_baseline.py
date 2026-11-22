#!/usr/bin/env python3
"""Gamma baseline: the composed Lockheed Martin state machines as one Gamma synchronous statechart, checked for
reachability of every composite state with Theta through the headless Gamma Docker image (ftsrggamma/headless-gamma).

Gamma has no SysML v2 importer, so the statechart is generated from the compiler's intermediate representation:
  * each SysML v2 state machine is an orthogonal region, in model order, scheduled sequentially, with guards evaluated
    on the fly and order-based transition priority (the compiler's default priority semantics);
  * the environment inputs (standby, apfail, supported, limits) are parameters of one input event 'step'; every
    transition is triggered by it, so a cycle without the event is a stutter, which adds no reachable state;
  * signals defined by glossary axioms are replaced by their definitions; a definition over the current state of a
    machine reads its region before that region moves (good = not in FAULT), and a definition over the next state
    reads it after (mode, request), which is why the autopilot region is scheduled first. The generator refuses any
    guard whose reading would depend on the opposite order.
The property file has one 'E F' query per composite state; Theta answers each with a witness or a proof.

    python3 baselines/gamma/gamma_baseline.py [OUTDIR]
Gamma 2.6.0 (the version in the image) generates the XSTS model; the queries are then run with the Theta XSTS
checker shipped in the same image, because the image's back-annotation step fails on a wrapped statechart.
"""
import itertools, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import (is_and, is_or, is_not, is_implies, is_eq, is_distinct, is_true, is_false, is_int_value, is_const,
                is_bool, substitute, Bool, Int)
from semantics import compile_model
import analysis


def gamma_project(model, out, project="LMGamma"):
    S = compile_model(model)
    ir = S.ir
    machines = list(ir["machines"])
    mv = {m: S.machine_vars(m) for m in machines}
    region = {m: ("r" + m) for m in machines}
    cur = {str(mv[m][1]): m for m in machines}
    nxt = {str(mv[m][2]): m for m in machines}
    lits = {m: S.enums[mv[m][0]] for m in machines}
    # glossary definitions of Boolean signals
    defs = {}
    for k, f in S.R.items():
        if analysis.is_glossary(k):
            for c in (f.children() if is_and(f) else [f]):
                if is_eq(c) and is_const(c.arg(0)) and is_bool(c.arg(0)):
                    defs[str(c.arg(0))] = c.arg(1)
    inputs = set()

    def gx(e, here):
        """z3 -> Gamma expression for a guard of machine 'here' (index in schedule)."""
        if is_true(e): return "true"
        if is_false(e): return "false"
        if is_not(e): return f"(not {gx(e.arg(0), here)})"
        if is_and(e): return "(" + " and ".join(gx(c, here) for c in e.children()) + ")"
        if is_or(e): return "(" + " or ".join(gx(c, here) for c in e.children()) + ")"
        if is_implies(e): return f"({gx(e.arg(0), here)} imply {gx(e.arg(1), here)})"
        if (is_eq(e) or is_distinct(e)) and not is_bool(e.arg(0)):
            a, b = e.arg(0), e.arg(1)
            if is_int_value(a): a, b = b, a
            v, k = str(a), b.as_long()
            if v in cur:
                m = cur[v]
                if machines.index(m) < here:
                    raise ValueError(f"guard of {machines[here]} reads the current state of {m}, already updated")
            elif v in nxt:
                m = nxt[v]
                if machines.index(m) > here:
                    raise ValueError(f"guard of {machines[here]} reads the next state of {m}, not yet updated")
            else:
                raise ValueError(f"unexpected integer variable {v}")
            s = f"in-state({region[m]}.{lits[m][k]}_{m})"
            return s if is_eq(e) else f"(not {s})"
        if is_eq(e):
            return f"({gx(e.arg(0), here)} = {gx(e.arg(1), here)})"
        if is_const(e):
            n = str(e)
            if n in defs:
                return gx(defs[n], here)
            inputs.add(n)
            return f"env.step::{n}"
        raise ValueError(str(e))

    trans = []
    for i, m in enumerate(machines):
        for t in ir["machines"][m]["transitions"]:
            trans.append(f"\ttransition from {t['src']}_{m} to {t['dst']}_{m} when env.step [{gx(S.E(t['guard']), i)}]")
    regions = []
    for m in machines:
        st = "\n".join(f"\t\tstate {s}_{m}" for s in ir["machines"][m]["states"])
        regions.append(f"\tregion {region[m]} {{\n\t\tinitial init_{m}\n{st}\n\t}}")
        trans.insert(0, f"\ttransition from init_{m} to {ir['machines'][m]['init']}_{m}")
    params = ", ".join(f"{n} : boolean" for n in sorted(inputs))
    gcd = f"""package lmgamma
// Generated from {os.path.basename(model)} by baselines/gamma/gamma_baseline.py
interface Env {{
	in event step({params})
}}
@OrthogonalRegionSchedule = sequential
@GuardEvaluation = on-the-fly
@TransitionPriority = order-based
statechart LMFSM [
	port env : provides Env
] {{
""" + "\n".join(regions) + "\n" + "\n".join(trans) + """
}
cascade LMSystem [
	port env : provides Env
] {
	component lmfsm : LMFSM
	bind env -> lmfsm.env
}
"""
    md = os.path.join(out, "model")       # Gamma 2.6 expects the models in a folder below the project root
    os.makedirs(md, exist_ok=True)
    open(os.path.join(md, "LMFSM.gcd"), "w").write(gcd)
    combos = list(itertools.product(*[ir["machines"][m]["states"] for m in machines]))
    q = []
    for c in combos:
        conj = " and ".join(f"state lmfsm.{region[m]}.{s}_{m}" for m, s in zip(machines, c))
        q.append(f'@("reach_{"_".join(c)}")\nE F [ {{ {conj} }} ]')
    # one Theta property per composite state, over the XSTS that Gamma generates for the statechart (region
    # variables <region>_LMFSM): the invariant 'not in this state' is Safe iff the state is unreachable
    os.makedirs(os.path.join(md, "q"), exist_ok=True)
    for i, c in enumerate(combos):
        e = " && ".join(f"{region[m]}_LMFSM == {s_}_{m}" for m, s_ in zip(machines, c))
        open(os.path.join(md, "q", f"q{i:02d}.prop"), "w").write(f"prop {{ !({e}) }}\n")
    open(os.path.join(md, "run.ggen"), "w").write("""import "LMFSM.gcd"

analysis {
	component : LMSystem
	language : Theta
}
""")

    open(os.path.join(out, ".project"), "w").write(f"""<?xml version="1.0" encoding="UTF-8"?>
<projectDescription>
	<name>{project}</name>
	<comment></comment>
	<projects></projects>
	<buildSpec></buildSpec>
	<natures></natures>
</projectDescription>
""")
    return S, gcd, combos, q, region


RUN = r"""
E=/home/headless/headless_eclipse/eclipse/eclipse; W=/workspaces/ws
$E -consoleLog -data $W workspace info >/dev/null 2>&1
$E -consoleLog -data $W import info LMGamma >/dev/null 2>&1
echo '{"underOperation": true}' > $W/LMGamma/projectDescriptor.json
$E -consoleLog -data $W gamma info $W/LMGamma/model/run.ggen $W/LMGamma/projectDescriptor.json > /workspaces/gamma.log 2>&1
cd $W/LMGamma/model
for f in q/*.prop; do
  echo "$f $(java -jar /home/theta/theta-xsts-cli.jar --domain EXPL --refinement SEQ_ITP --maxenum 250 --initprec CTRL \
        --model LMFSM.xsts --property $f 2>&1 | grep -o 'SafetyResult [A-Za-z]*' | head -1)"
done > /workspaces/theta.txt
"""


def run(model, out, image="ftsrggamma/headless-gamma"):
    import json, shutil, subprocess, time, zipfile
    out = os.path.abspath(out)
    shutil.rmtree(out, ignore_errors=True)
    proj = os.path.join(out, "LMGamma")
    S, gcd, combos, q, region = gamma_project(model, proj)
    ws = os.path.join(out, "workspaces", "ws"); os.makedirs(ws)
    with zipfile.ZipFile(os.path.join(ws, "LMGamma.zip"), "w") as z:
        for dp, _, fs in os.walk(proj):
            for f in fs:
                z.write(os.path.join(dp, f), os.path.relpath(os.path.join(dp, f), out))
    open(os.path.join(out, "workspaces", "run.sh"), "w").write(RUN)
    t = time.time()
    subprocess.run(["docker", "run", "--rm", "-v", f"{out}/workspaces:/workspaces", "--entrypoint", "/bin/bash", image,
                    "/workspaces/run.sh"], check=True, capture_output=True, timeout=3600)
    dt = time.time() - t
    shutil.copy(os.path.join(ws, "LMGamma", "model", "LMFSM.xsts"), os.path.join(out, "LMFSM.xsts"))
    verdicts = {}
    for line in open(os.path.join(out, "workspaces", "theta.txt")):
        f, *r = line.split()
        verdicts[int(re.search(r"q(\d+)", f).group(1))] = r[-1] if r else "unknown"
    machines = list(S.ir["machines"])
    reach = [dict(zip(machines, c)) for i, c in enumerate(combos) if verdicts.get(i) == "Unsafe"]
    unreach = [dict(zip(machines, c)) for i, c in enumerate(combos) if verdicts.get(i) == "Safe"]
    import analysis
    comp = analysis.reachable_situations(S, analysis.check_machines(S))["states"]
    res = dict(model=os.path.basename(model), composite_states=len(combos), reachable_gamma_theta=sorted(reach, key=str),
               unreachable_gamma_theta=sorted(unreach, key=str), reachable_compiler=comp,
               agree=sorted(reach, key=str) == comp and len(reach) + len(unreach) == len(combos), seconds=round(dt, 1))
    json.dump(res, open(os.path.join(out, "gamma_reachability.json"), "w"), indent=1)
    shutil.rmtree(os.path.join(out, "workspaces"))
    print(f"{res['model']}: Gamma/Theta {len(reach)} reachable, {len(unreach)} unreachable; agree={res['agree']} ({dt:.0f} s)")
    return res


if __name__ == "__main__":
    # python3 baselines/gamma/gamma_baseline.py [OUTDIR]   (needs Docker and the image ftsrggamma/headless-gamma)
    outs = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "results", "reference", "gamma")
    for m in ("lmcps_fsm", "lmcps_fsm_rev"):
        run(os.path.join(ROOT, "models", m + ".sysml"), os.path.join(outs, m))
