"""EDA back end: IR -> Verilog netlists -> Yosys/ABC.

* Models with state machines: one sequential module 'design' (machines as registers, glossary definitions as
  wires, preK_x history registers) with one assertion per requirement, each proved separately by temporal
  induction (sat -tempinduct). A combinational module 'reqs' has one output per requirement; ABC reports its
  AND-inverter-graph size before and after optimisation.
* Models with variability: a combinational module 'cfg' whose inputs are the variant-selection and allocation
  bits and whose outputs are the requirements; arithmetic is folded to truth tables by evaluating the physics for
  every selection (constant propagation), then minimised to sum-of-products. Dead/core variants are proved by SAT.
"""
import itertools, math, os, re, subprocess
from z3 import (is_and, is_or, is_not, is_implies, is_eq, is_distinct, is_true, is_false, is_int_value, is_const,
                is_app_of, Z3_OP_ITE, BoolVal, And, Not, simplify, substitute, IntVal, is_bool)
from sympy import symbols
from sympy.logic import SOPform

YOSYS = "yowasp-yosys"


def vexpr(e):
    if is_true(e): return "1'b1"
    if is_false(e): return "1'b0"
    if is_int_value(e): return str(e.as_long())
    if is_not(e): return f"!({vexpr(e.arg(0))})"
    if is_and(e): return "(" + " && ".join(vexpr(c) for c in e.children()) + ")"
    if is_or(e): return "(" + " || ".join(vexpr(c) for c in e.children()) + ")"
    if is_implies(e): return f"(!({vexpr(e.arg(0))}) || ({vexpr(e.arg(1))}))"
    if is_eq(e): return f"({vexpr(e.arg(0))} == {vexpr(e.arg(1))})"
    if is_distinct(e): return f"({vexpr(e.arg(0))} != {vexpr(e.arg(1))})"
    if is_app_of(e, Z3_OP_ITE): return f"(({vexpr(e.arg(0))}) ? ({vexpr(e.arg(1))}) : ({vexpr(e.arg(2))}))"
    if is_const(e): return str(e)
    raise ValueError(f"cannot translate {e}")


def width(n):
    return max(1, math.ceil(math.log2(n)))


def run_yosys(script, cwd, timeout=900):
    p = subprocess.run([YOSYS, "-p", script], cwd=cwd, capture_output=True, text=True, timeout=timeout)
    return p.stdout + p.stderr


def gate_count(log):
    blk = log.split("Printing statistics")[-1]
    get = lambda pat: sum(int(x) for x in re.findall(r"(\d+)\s+\$_" + pat + r"_", blk))
    return dict(AND=get("AND"), NOT=get("NOT"), FF=get(r"(?:S?DFF\w*|DFFE\w*)"))


def aig_stats(src, top, cwd, formal=False):
    """AND-inverter graph size as written (techmap+aigmap) and after logic optimisation
    (Yosys synth without ABC, SAT-based functional reduction 'freduce' = fraiging, re-mapped to AIG)."""
    rd = f"read_verilog {'-formal ' if formal else ''}{src}"
    raw = run_yosys(f"{rd}; hierarchy -top {top}; proc; flatten; opt_clean; techmap; aigmap; opt_clean; stat", cwd)
    opt = run_yosys(f"{rd}; synth -flatten -noabc -top {top}; aigmap; freduce; opt_clean; opt -full; aigmap; opt_clean; stat", cwd)
    return dict(as_written=gate_count(raw), optimized=gate_count(opt))


# ------------------------------------------------------------------ sequential designs
def emit_design(S, outdir):
    ir = S.ir
    glo = {k: f for k, f in S.R.items() if k.startswith("GLO")}
    props = {k: f for k, f in S.R.items() if not k.startswith("GLO")}
    defs = {}                                                     # signal -> z3 expr
    for k, f in glo.items():
        for c in (f.children() if is_and(f) else [f]):
            if is_eq(c) and is_const(c.arg(0)) and is_bool(c.arg(0)):
                defs[str(c.arg(0))] = c.arg(1)
    mach = {}
    for m in ir["machines"]:
        enum, cur, nxt = S.machine_vars(m)
        mach[m] = (enum, cur, nxt)
    pre = sorted({n for f in props.values() for n in re.findall(r"\bpre(\d+)_(\w+)", str(f)) for n in [n]}, key=lambda x: (x[1], int(x[0])))
    hist = {}
    for k, x in pre:
        hist[x] = max(hist.get(x, 0), int(k))
    defined = set(defs) | {str(c) for _, c, _ in mach.values()} | {str(n) for _, _, n in mach.values()} \
        | {f"pre{k}_{x}" for x, d in hist.items() for k in range(1, d + 1)}
    used = set()
    for f in list(props.values()) + list(defs.values()):
        used |= set(re.findall(r"\b[A-Za-z_]\w*\b", str(f)))
    for m in ir["machines"].values():
        for t in m["transitions"]:
            used |= {x.split(".")[-1] for x in re.findall(r"[A-Za-z_][\w.]*", t["guard"])}
    kw = {"And", "Or", "Not", "Implies", "If", "and", "or", "not", "True", "False"}
    inputs = sorted(n for n in used if n in S.vars and S.vtype.get(n) == "Boolean" and n not in defined and n not in kw)
    L = ["module design(input clk" + "".join(f", input {n}" for n in inputs) + "".join(f", output {n}" for n in defs) + ");"]
    for m, (enum, cur, nxt) in mach.items():
        w = width(len(S.enums[enum])); init = S.enums[enum].index(ir["machines"][m]["init"])
        L.append(f"  reg [{w - 1}:0] {cur}; initial {cur} = {w}'d{init};")
        L.append(f"  wire [{w - 1}:0] {nxt};")
    for x, d in hist.items():
        for k in range(1, d + 1):
            L.append(f"  reg pre{k}_{x}; initial pre{k}_{x} = 1'b0;")
    for n, e in defs.items():
        L.append(f"  assign {n} = {vexpr(e)};")
    for m, (enum, cur, nxt) in mach.items():
        lits = S.enums[enum]
        expr = str(cur)
        for s in reversed(ir["machines"][m]["states"]):
            chain = str(cur)                                    # stay
            for t in reversed([t for t in ir["machines"][m]["transitions"] if t["src"] == s]):
                chain = f"({vexpr(S.E(t['guard']))}) ? {lits.index(t['dst'])} : ({chain})"
            expr = f"({cur} == {lits.index(s)}) ? ({chain}) : ({expr})"
        L.append(f"  assign {nxt} = {expr};")
    L.append("  always @(posedge clk) begin")
    for m, (enum, cur, nxt) in mach.items():
        L.append(f"    {cur} <= {nxt};")
    for x, d in hist.items():
        L.append(f"    pre1_{x} <= {x};")
        for k in range(2, d + 1):
            L.append(f"    pre{k}_{x} <= pre{k - 1}_{x};")
    L.append("  end")
    for k, f in props.items():
        tag = re.sub(r"\W", "_", k)
        L.append(f"`ifdef P_{tag}\n  always @* assert ({vexpr(f)});\n`endif")
    L.append("endmodule")
    path = os.path.join(outdir, "design.sv")
    open(path, "w").write("\n".join(L) + "\n")
    # combinational module with one output per requirement (logic view as netlist)
    allv = sorted({n for f in S.R.values() for n in re.findall(r"\b[A-Za-z_]\w*\b", str(f)) if n in S.vars})
    ports = []
    for n in allv:
        ty = S.vtype[n]
        ports.append(f"input [{width(len(S.enums[ty])) - 1}:0] {n}" if ty in S.enums else f"input {n}")
    R2 = [f"module reqs({', '.join(ports + [f'output r_{re.sub(chr(92) + 'W', '_', k)}' for k in S.R if not any(p in str(S.R[k]) for p in ('pre1_',))])});"]
    for k, f in S.R.items():
        if "pre1_" in str(f):
            continue
        R2.append(f"  assign r_{re.sub(r'\W', '_', k)} = {vexpr(f)};")
    R2.append("endmodule")
    open(os.path.join(outdir, "reqs.v"), "w").write("\n".join(R2) + "\n")
    return path, list(props), inputs


def prove_design(S, outdir):
    path, props, inputs = emit_design(S, outdir)
    res = {}
    for k in props:
        tag = re.sub(r"\W", "_", k)
        log = run_yosys(f"read_verilog -formal -DP_{tag} design.sv; prep -top design; chformal -lower; "
                        f"select -assert-min 1 t:$assert; "
                        f"sat -tempinduct -prove-asserts -maxsteps 30 -show-inputs", outdir)
        open(os.path.join(outdir, f"yosys_{tag}.log"), "w").write(log)
        if "Assertion failed" in log or "ERROR" in log:
            res[k] = dict(result="error (no assertion compiled)", tail=log[-300:])
        elif "SUCCESS" in log:
            n = re.findall(r"Trying induction with length (\d+)", log)
            res[k] = dict(result="proved", induction_length=int(n[-1]) if n else None)
        elif "FAIL" in log:
            n = re.findall(r"Trying induction with length (\d+)", log)
            res[k] = dict(result="counterexample", trace_length=int(n[-1]) if n else None)
        else:
            res[k] = dict(result="inconclusive", tail=log[-300:])
    reqs_stats = aig_stats("reqs.v", "reqs", outdir)
    design_stats = aig_stats("design.sv", "design", outdir)
    import ic3
    for k, v in res.items():
        if v["result"] == "inconclusive" or "pre1_" in str(S.R[k]):
            runs = [ic3.prove(S, k, seed=sd) for sd in range(5)]
            r = runs[0]
            v["ic3"] = dict(result=r["result"])
            if r.get("invariant_expr") is not None:
                mins = [pretty_lemmas(S, x["invariant_min_expr"]) for x in runs]
                v["ic3"].update(lemmas=pretty_lemmas(S, r["invariant_expr"]),
                                clauses_found=[x["n_clauses_found"] for x in runs],
                                clauses_minimal=[x["n_clauses_min"] for x in runs],
                                lemmas_minimal=mins[0],
                                lemmas_in_every_minimal_set=sorted(set(mins[0]).intersection(*map(set, mins[1:]))))
            if v["result"] == "inconclusive":
                v["result"] = r["result"] + " (IC3)"
    return dict(properties=res, aig_requirements=reqs_stats, aig_design=design_stats, inputs=inputs)


# ------------------------------------------------------------------ variability as a combinational configuration circuit
def emit_cfg(S, var_res, outdir):
    U = list(S.usages)
    names = var_res["variations"]
    funs = var_res["allocation_functions"]
    bits = {u: width(len(names[u])) for u in U}
    R = dict(S.R)
    if "CAP" not in R and funs:
        pass
    from analysis import check_variability  # noqa: F401  (CAP is rebuilt the same way)
    acts = {n: a for ad in S.ir["actions"].values() for n, a in ad["attrs"].items()}
    from z3 import If, RealVal, Bool
    fixed = [f for f in funs if acts[f].get("fixedOnBoard")]
    cap_u = next((u for u in U if all("cpuCapacity" in a for _, a in S.ir["variations"][S.usages[u]])), None)
    if funs and cap_u:
        R["CAP"] = sum(If(S.onboard[f], RealVal(acts[f]["cpuLoad"]), RealVal(0)) for f in funs) <= S.variant_attr(cap_u, "cpuCapacity")
    free = [f for f in funs if f not in fixed]
    inames = [f"{u}_b{i}" for u in U for i in range(bits[u])] + [f"onboard_{f}" for f in free]
    sy = symbols(" ".join(inames)); sy = sy if isinstance(sy, tuple) else (sy,)
    tables = {k: [] for k in R}
    valid_code = []
    for combo in itertools.product([0, 1], repeat=len(inames)):
        pos, sub, ok = 0, [], True
        for u in U:
            code = int("".join(map(str, combo[pos:pos + bits[u]])), 2); pos += bits[u]
            if code >= len(names[u]):
                ok = False
            sub.append((S.sel[u], IntVal(min(code, len(names[u]) - 1))))
        for f in funs:
            v = BoolVal(True) if f in fixed else BoolVal(bool(combo[pos + free.index(f)]))
            sub.append((S.onboard[f], v))
        if ok:
            valid_code.append(list(combo))
        for k, f in R.items():
            if ok and is_true(simplify(substitute(f, *sub))):
                tables[k].append(list(combo))
    L = [f"module cfg({', '.join('input ' + n for n in inames)}, " + ", ".join(f"output r_{re.sub(r'\W', '_', k)}" for k in R) + ", output legal, output valid);"]
    for k, ones in tables.items():
        e = SOPform(list(sy), ones) if ones else False
        L.append(f"  assign r_{re.sub(r'\W', '_', k)} = {sym2v(e)};")
    L.append(f"  assign legal = {sym2v(SOPform(list(sy), valid_code))};")
    L.append("  assign valid = legal && " + " && ".join(f"r_{re.sub(r'\W', '_', k)}" for k in R) + ";")
    # dead / core variant properties
    for u in U:
        for k, n in enumerate(names[u]):
            code = format(k, f"0{bits[u]}b")
            sel = " && ".join(f"{u}_b{i} == 1'b{c}" for i, c in enumerate(code))
            tag = f"{u}_{n}"
            L.append(f"`ifdef DEAD_{tag}\n  always @* assert (!(valid && {sel}));\n`endif")
            L.append(f"`ifdef CORE_{tag}\n  always @* assert (!valid || ({sel}));\n`endif")
    L.append("endmodule")
    open(os.path.join(outdir, "cfg.sv"), "w").write("\n".join(L) + "\n")
    return names, tables


def sym2v(e):
    if e is False or str(e) == "False":
        return "1'b0"
    if str(e) == "True":
        return "1'b1"
    return str(e).replace("&", "&&").replace("|", "||").replace("~", "!")


def prove_cfg(S, var_res, outdir):
    names, tables = emit_cfg(S, var_res, outdir)
    res = {}
    # precondition: at least one valid configuration (otherwise every variant would be both dead and core)
    log = run_yosys("read_verilog -formal cfg.sv; prep -top cfg; sat -prove valid 0", outdir)
    if "SUCCESS" in log:
        return dict(proved={}, inconsistent=True, aig_cfg=aig_stats("cfg.sv", "cfg", outdir, formal=True),
                    truth_table_ones={k: len(v) for k, v in tables.items()})
    for u, vs in names.items():
        for n in vs:
            for kind in ("DEAD", "CORE"):
                tag = f"{kind}_{u}_{n}"
                log = run_yosys(f"read_verilog -formal -D{tag} cfg.sv; prep -top cfg; chformal -lower; "
                                f"select -assert-min 1 t:$assert; sat -prove-asserts", outdir)
                if "ERROR" not in log and "SUCCESS" in log:
                    res[f"{kind.lower()}:{u}.{n}"] = "proved"
    cfg_stats = aig_stats("cfg.sv", "cfg", outdir, formal=True)
    return dict(proved=res, aig_cfg=cfg_stats,
                truth_table_ones={k: len(v) for k, v in tables.items()})


def pretty_lemmas(S, inv):
    """Inductive invariant as readable clauses, with enumeration comparisons rewritten as state sets."""
    from z3 import is_and, is_or, is_not, is_le, is_ge, is_eq
    enum_of = {}
    for m in S.ir["machines"]:
        enum, cur, _ = S.machine_vars(m)
        enum_of[str(cur)] = S.enums[enum]
    def lit(e):
        neg = is_not(e)
        a = e.arg(0) if neg else e
        txt = None
        if (is_le(a) or is_ge(a) or is_eq(a)) and str(a.arg(0)) in enum_of:
            v, k = str(a.arg(0)), a.arg(1).as_long()
            L = enum_of[v]
            idx = [i for i in range(len(L)) if (i <= k if is_le(a) else i >= k if is_ge(a) else i == k)]
            if neg:
                idx = [i for i in range(len(L)) if i not in idx]
            return f"{v} ∈ {{{', '.join(L[i] for i in idx)}}}"
        if (is_le(a) or is_ge(a) or is_eq(a)) and str(a.arg(1)) in enum_of:
            v, k = str(a.arg(1)), a.arg(0).as_long()
            L = enum_of[v]
            idx = [i for i in range(len(L)) if (i >= k if is_le(a) else i <= k if is_ge(a) else i == k)]
            if neg:
                idx = [i for i in range(len(L)) if i not in idx]
            return f"{v} ∈ {{{', '.join(L[i] for i in idx)}}}"
        return ("¬" if neg else "") + str(a)
    cls = inv.children() if is_and(inv) else [inv]
    out = []
    for c in cls:
        ls = c.children() if is_or(c) else [c]
        out.append(" ∨ ".join(lit(l) for l in ls))
    return out
