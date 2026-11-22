#!/usr/bin/env python3
"""Emit the sequential semantics of a SysML model as a Lustre node (machines as 'x = init -> pre next', glossary as
equations, preK_x as delayed streams initially false) with one property per requirement, and model-check it with
Kind 2. Used as an independent cross-check of the Yosys / IC3 verdicts.

    python3 lustre.py MODEL.sysml OUTDIR
"""
import json, os, re, subprocess, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import (is_and, is_or, is_not, is_implies, is_eq, is_distinct, is_true, is_false, is_int_value, is_const,
                is_app_of, Z3_OP_ITE, is_bool)
from parser import parse
from semantics import Semantics, compile_model
import analysis

KIND2 = os.environ.get("KIND2", "kind2")


def lx(e):
    if is_true(e): return "true"
    if is_false(e): return "false"
    if is_int_value(e): return str(e.as_long())
    if is_not(e): return f"(not {lx(e.arg(0))})"
    if is_and(e): return "(" + " and ".join(lx(c) for c in e.children()) + ")"
    if is_or(e): return "(" + " or ".join(lx(c) for c in e.children()) + ")"
    if is_implies(e): return f"({lx(e.arg(0))} => {lx(e.arg(1))})"
    if is_eq(e): return f"({lx(e.arg(0))} = {lx(e.arg(1))})"
    if is_distinct(e): return f"({lx(e.arg(0))} <> {lx(e.arg(1))})"
    if is_app_of(e, Z3_OP_ITE): return f"(if {lx(e.arg(0))} then {lx(e.arg(1))} else {lx(e.arg(2))})"
    if is_const(e): return "v_" + str(e)
    raise ValueError(str(e))


def emit(S, path):
    ir = S.ir
    analysis.machine_groups(S)
    glo = {k: f for k, f in S.R.items() if k.startswith("GLO")}
    props = {k: f for k, f in S.R.items() if not k.startswith("GLO")}
    defs = {}
    for f in glo.values():
        for c in (f.children() if is_and(f) else [f]):
            if is_eq(c) and is_const(c.arg(0)) and is_bool(c.arg(0)):
                defs[str(c.arg(0))] = c.arg(1)
    mach = {m: S.machine_vars(m) for m in ir["machines"]}
    hist = {}
    for f in props.values():
        for k, x in re.findall(r"\bpre(\d+)_(\w+)", str(f)):
            hist[x] = max(hist.get(x, 0), int(k))
    defined = set(defs) | {str(c) for _, c, _ in mach.values()} | {str(n) for _, _, n in mach.values()} \
        | {f"pre{k}_{x}" for x, d in hist.items() for k in range(1, d + 1)}
    used = set()
    for f in list(props.values()) + list(defs.values()):
        used |= set(re.findall(r"\b[A-Za-z_]\w*\b", str(f)))
    for m in ir["machines"].values():
        for t in m["transitions"]:
            used |= {x.split(".")[-1] for x in re.findall(r"[A-Za-z_][\w.]*", t["guard"])}
    inputs = sorted(n for n in used if S.vtype.get(n) == "Boolean" and n not in defined and n in S.vars)
    L = ["node design(" + "; ".join(f"v_{n}: bool" for n in inputs) + ") returns (" +
         "; ".join(f"ok_{re.sub(r'\W', '_', k)}: bool" for k in props) + ");", "var"]
    for _, cur, nxt in mach.values():
        L.append(f"  v_{cur}, v_{nxt}: int;")
    for n in defs:
        L.append(f"  v_{n}: bool;")
    for x, d in hist.items():
        for k in range(1, d + 1):
            L.append(f"  v_pre{k}_{x}: bool;")
    L.append("let")
    for m, (enum, cur, nxt) in mach.items():
        lits = S.enums[enum]; init = lits.index(ir["machines"][m]["init"])
        L.append(f"  v_{cur} = {init} -> pre v_{nxt};")
        expr = f"v_{cur}"
        for s in reversed(ir["machines"][m]["states"]):
            chain = f"v_{cur}"
            for t in reversed([t for t in ir["machines"][m]["transitions"] if t["src"] == s]):
                chain = f"(if {lx(S.E(t['guard']))} then {lits.index(t['dst'])} else {chain})"
            expr = f"(if v_{cur} = {lits.index(s)} then {chain} else {expr})"
        L.append(f"  v_{nxt} = {expr};")
    for n, e in defs.items():
        L.append(f"  v_{n} = {lx(e)};")
    for x, d in hist.items():
        L.append(f"  v_pre1_{x} = false -> pre v_{x};")
        for k in range(2, d + 1):
            L.append(f"  v_pre{k}_{x} = false -> pre v_pre{k - 1}_{x};")
    for k, f in props.items():
        tag = re.sub(r"\W", "_", k)
        L.append(f"  ok_{tag} = {lx(f)};")
        L.append(f"  --%PROPERTY \"{k}\" ok_{tag};")
    L.append("tel")
    open(path, "w").write("\n".join(L) + "\n")
    return list(props)


def check(path, timeout=600):
    t = time.time()
    out = subprocess.run([KIND2] + (["--z3_bin", os.environ["Z3_BIN"]] if os.environ.get("Z3_BIN") else []) + ["--color", "false", "--timeout", "300", path],
                         capture_output=True, text=True, timeout=timeout).stdout
    res = {}
    for name, verdict in re.findall(r'Property "?([\w\-]+)"? is (valid|invalid|unknown)', out):
        res[name] = verdict
    for name in re.findall(r'Property "?([\w\-]+)"? is valid', out):
        res[name] = "valid"
    return res, time.time() - t, out


if __name__ == "__main__":
    S = compile_model(sys.argv[1])
    os.makedirs(sys.argv[2], exist_ok=True)
    p = os.path.join(sys.argv[2], "design.lus")
    emit(S, p)
    res, dt, out = check(p)
    open(os.path.join(sys.argv[2], "kind2.log"), "w").write(out)
    json.dump(dict(results=res, seconds=dt), open(os.path.join(sys.argv[2], "kind2.json"), "w"), indent=1)
    print(json.dumps(res, indent=1), f"\n{dt:.1f} s")
