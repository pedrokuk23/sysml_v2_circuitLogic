#!/usr/bin/env python3
"""Semantic difference of two versions of a SysML v2 requirement set, as EDA combinational equivalence checking.

    python3 diff.py OLD.sysml NEW.sysml -o OUTDIR

For every requirement present in both versions, a miter (old XOR new) is built as a Verilog module and Yosys proves
equivalence or returns a distinguishing input; the exact region where the two versions differ is computed by
quantifier elimination. For each state machine, the set-level check asks where the ALLOWED next states differ, and
whether the versions are conditionally equivalent on the situations where the old set is satisfiable.
"""
import argparse, json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import And, Or, Not, Xor, Exists, ForAll, Implies, BoolVal
from parser import parse
from semantics import Semantics, compile_model
import analysis, verilog
from logic_engine import is_sat, valid, finite_region


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("old"); ap.add_argument("new"); ap.add_argument("-o", "--out", default="out_diff")
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
    So, Sn = compile_model(a.old), compile_model(a.new)
    go, gn = analysis.machine_groups(So), analysis.machine_groups(Sn)
    dom = And(So.domain, Sn.domain)
    res = dict(old=a.old, new=a.new, requirements={}, sets={})
    # ---- requirement-level miters
    common = [k for k in So.R if k in Sn.R]
    changed = [k for k in common if not valid(So.R[k] == Sn.R[k], dom)[0]]
    res["added"] = [k for k in Sn.R if k not in So.R]; res["removed"] = [k for k in So.R if k not in Sn.R]
    ports, lines, names = set(), [], {}
    for k in changed:
        tag = re.sub(r"\W", "_", k)
        names[k] = tag
        lines.append(f"  assign old_{tag} = {verilog.vexpr(So.R[k])};")
        lines.append(f"  assign new_{tag} = {verilog.vexpr(Sn.R[k])};")
        lines.append(f"`ifdef M_{tag}\n  always @* assert (old_{tag} == new_{tag});\n`endif")
        ports |= set(re.findall(r"\b[A-Za-z_]\w*\b", str(So.R[k]) + " " + str(Sn.R[k])))
    ports = sorted(p for p in ports if p in So.vars or p in Sn.vars)
    decl = []
    for p in ports:
        ty = So.vtype.get(p) or Sn.vtype.get(p)
        decl.append(f"input [{verilog.width(len(So.enums[ty])) - 1}:0] {p}" if ty in So.enums else f"input {p}")
    outs = [f"output old_{t}, output new_{t}" for t in names.values()]
    open(os.path.join(a.out, "miter.sv"), "w").write(f"module miter({', '.join(decl + outs)});\n" + "\n".join(lines) + "\nendmodule\n")
    for k in changed:
        tag = names[k]
        log = verilog.run_yosys(f"read_verilog -formal -DM_{tag} miter.sv; prep -top miter; chformal -lower; "
                                f"select -assert-min 1 t:$assert; sat -prove-asserts -show-inputs", a.out)
        open(os.path.join(a.out, f"yosys_miter_{tag}.log"), "w").write(log)
        verdict = "equivalent" if "SUCCESS" in log else ("different" if "FAIL" in log else "error")
        d = And(dom, Xor(So.R[k], Sn.R[k]))
        bools = sorted({b for b in analysis.bools_in(d, So)} | {b for b in analysis.bools_in(d, Sn)}, key=str)
        en = {}
        for m, g in go.items():
            if str(g["cur"]) in str(d):
                en[g["cur"]] = dict(enumerate(So.enums[g["enum"]]))
        ins = [b for b in bools]
        region = finite_region(Exists([g["nxt"] for g in go.values()], d), ins, en)
        stronger = "new ⇒ old" if valid(Implies(Sn.R[k], So.R[k]), dom)[0] else ("old ⇒ new" if valid(Implies(So.R[k], Sn.R[k]), dom)[0] else "incomparable")
        res["requirements"][k] = dict(yosys=verdict, differ_where=region, order=stronger)
    # ---- set-level: allowed next states per machine
    allnext = [g["nxt"] for g in go.values()]
    indom = And(*[And(g["cur"] >= 0, g["cur"] < len(So.enums[g["enum"]])) for g in go.values()])
    for m in go:
        nxt = go[m]["nxt"]; cur = go[m]["cur"]
        Ao = And(*go[m]["reqs"].values()); An = And(*gn[m]["reqs"].values())
        sat_old = Exists(allnext, And(dom, Ao))
        cond_eq = valid(Implies(sat_old, Ao == An), And(indom, dom))[0]
        ins = sorted({b for f in list(go[m]["reqs"].values()) + list(gn[m]["reqs"].values()) for b in analysis.bools_in(f, So)}, key=str)
        en = {cur: dict(enumerate(So.enums[go[m]["enum"]]))}
        diff_region = finite_region(And(indom, Exists(allnext, And(dom, Xor(Ao, An)))), ins, en)
        conflict_old = finite_region(And(indom, Not(sat_old)), ins, en)
        res["sets"][m] = dict(conditionally_equivalent_where_old_satisfiable=cond_eq,
                              differ_where=diff_region, old_conflict_region=conflict_old,
                              difference_equals_old_conflicts=valid(Exists(allnext, And(dom, Xor(Ao, An))) == Not(sat_old), indom)[0])
    json.dump(res, open(os.path.join(a.out, "diff.json"), "w"), indent=1, ensure_ascii=False, default=str)
    print(json.dumps(res, indent=1, ensure_ascii=False, default=str))


if __name__ == "__main__":
    main()
