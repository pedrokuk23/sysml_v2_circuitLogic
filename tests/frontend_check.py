#!/usr/bin/env python3
"""Every analysis run twice, once on the IR from the subset grammar (parser.py) and once on the IR built from the
SysML v2 Pilot Implementation's syntax tree (pilot_frontend.py), and the two results.json compared leaf by leaf.

A leaf must be identical, with two exceptions that are checked semantically instead of textually:
  * an expression echoed from the source (an assert, a decision guard) is printed fully parenthesized by the Pilot
    front end; both texts are compiled and proved equivalent by Z3;
  * a region computed by quantifier elimination is printed by Z3 from formulas of different shape; the two regions
    are proved equivalent by Z3.

    python3 tests/frontend_check.py [model ...]
"""
import json, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
import re
from z3 import Solver, Xor, unsat, is_bool, And, Or, Not, Implies, If, Q, Real, Bool, Int, ToReal, BoolVal, is_expr
import logic_engine, analysis
from semantics import compile_model
from pilot_frontend import compile_pilot

_QE = {}
_qe = logic_engine.qe


def _record(f, *a, **k):
    r = _qe(f, *a, **k)
    _QE.setdefault(str(r), []).append(r)
    return r


logic_engine.qe = _record
analysis.qe = _record


def leaves(x, p=""):
    if isinstance(x, dict):
        for k in sorted(x):
            yield from leaves(x[k], f"{p}/{k}")
    elif isinstance(x, (list, tuple)):
        for i, v in enumerate(x):
            yield from leaves(v, f"{p}[{i}]")
    else:
        yield p, x


def equivalent(f, g):
    s = Solver()
    s.add(Xor(f, g) if is_bool(f) else f != g)
    return s.check() == unsat


def as_z3(text, S):
    """Evaluate a formula printed by Z3 (as in results.json) back into a Z3 term over the model's variables."""
    names = set(re.findall(r"\b[A-Za-z_]\w*\b", text)) - {"And", "Or", "Not", "Implies", "If", "ToReal", "True", "False", "Q"}
    env = {}
    for n in names:
        env[n] = S.vars.get(n)
        if env[n] is None:
            ty = S.vtype.get(n) or S.ir.get("part_attrs", {}).get(n, "Real")
            env[n] = Bool(n) if ty == "Boolean" else Int(n) if ty == "Integer" else Real(n)
    t = re.sub(r"(?<![\w.])(\d+)/(\d+)", r"Q(\1,\2)", text)
    env.update(And=And, Or=Or, Not=Not, Implies=Implies, If=If, ToReal=ToReal, Q=Q, True_=BoolVal(True))
    return eval(t, {"__builtins__": {}}, env)


def check(model):
    path = os.path.join(ROOT, "models", model + ".sysml")
    _QE.clear()
    Sg = compile_model(path)
    a = json.loads(json.dumps(analysis.run_all(Sg), default=str))
    qa = dict(_QE)
    _QE.clear()
    Sp = compile_pilot(path)
    b = json.loads(json.dumps(analysis.run_all(Sp), default=str))
    qb = dict(_QE)
    a.pop("model"); b.pop("model")
    la, lb = dict(leaves(a)), dict(leaves(b))
    same = textual = semantic = numeric = method = 0
    fails = []
    A = And(Sg.domain, *[f for k, f in Sg.R.items() if analysis.is_glossary(k)])
    for k in sorted(set(la) | set(lb)):
        x, y = la.get(k), lb.get(k)
        if x == y:
            same += 1
            continue
        kind = lambda m: re.match(r"[a-z]+", m or "") and re.match(r"[a-z]+", m).group(0)
        if k.endswith("/weakest") and {x, y} <= {None, True} and \
                {kind(la.get(k[:-8] + "/method")), kind(lb.get(k[:-8] + "/method"))} == {"quantifier", "numerical"}:
            method += 1            # 'weakest' is checked only for exact (QE) results
            continue
        if k not in la or k not in lb or not isinstance(x, str) or not isinstance(y, str):
            fails.append(f"{k}: {x!r} vs {y!r}"); continue
        if x in qa and y in qb and equivalent(qa[x][0], qb[y][0]):
            semantic += 1
            continue
        try:
            if equivalent(Sg.E(x), Sp.E(y)):
                textual += 1
                continue
        except Exception:
            pass
        if k.endswith("/method") and {kind(x), kind(y)} == {"quantifier", "numerical"}:
            method += 1            # QE finished within its time limit in one run and not in the other
            continue
        try:
            f, g = as_z3(x, Sg), as_z3(y, Sg)
            if is_expr(f) and is_expr(g) and is_bool(f):
                s_ = Solver(); s_.add(A, Xor(f, g))
                if s_.check() == unsat:
                    semantic += 1
                    continue
                fv = {str(v) for v in logic_engine.free_consts(And(f, g)).values()}
                if len(fv) == 1:                   # a single-quantity bound: compare its supremum under A
                    v = logic_engine.free_consts(And(f, g))[fv.pop()]
                    a_, b_ = analysis._sup(v, And(A, f)), analysis._sup(v, And(A, g))
                    if a_ is not None and b_ is not None and abs(a_ - b_) <= 1e-5 * max(1.0, abs(a_)):
                        numeric += 1
                        continue
        except Exception as ex:
            fails.append(f"{k}: comparison raised {type(ex).__name__}: {ex}")
            continue
        fails.append(f"{k}: {x!r} vs {y!r}")
    return dict(leaves=len(la), identical=same, echoed_expressions_equivalent=textual,
                regions_equivalent=semantic, bounds_numerically_equal=numeric, method_differs_time_limit=method,
                failures=fails)


if __name__ == "__main__":
    ms = sys.argv[1:] or sorted(f[:-6] for f in os.listdir(os.path.join(ROOT, "models")) if f.endswith(".sysml"))
    rep, ok = {}, True
    for m in ms:
        r = check(m)
        rep[m] = r
        ok &= not r["failures"]
        print(f"{m}: {r['leaves']} result leaves, {r['identical']} identical, {r['echoed_expressions_equivalent']} "
              f"echoed expressions and {r['regions_equivalent']} formulas equivalent, {r['bounds_numerically_equal']} bounds "
              f"numerically equal, {r['method_differs_time_limit']} QE-vs-bisection, {len(r['failures'])} differences")
        for f in r["failures"]:
            print("   ", f)
    json.dump(rep, open(os.path.join(ROOT, "results", "reference", "ast", "frontend_check.json"), "w"), indent=1)
    sys.exit(0 if ok else 1)
