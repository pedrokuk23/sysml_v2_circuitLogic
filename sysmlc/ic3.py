"""IC3/PDR (z3 Spacer) on the sequential semantics of the SysML model: proves a requirement as a safety property
over all reachable states and returns the inductive invariant it found — a lemma the requirement silently relies on.
Used when k-induction (Yosys) does not close."""
import re
from z3 import (Fixedpoint, Function, IntSort, BoolSort, Int, Bool, And, Not, Implies, BoolVal, substitute, is_and,
                is_eq, is_const, is_bool, simplify)


def prove(S, prop_id, seed=0):
    ir = S.ir
    mach = {m: S.machine_vars(m) for m in ir["machines"]}
    rels = [S.machine_relation(m) for m in ir["machines"]]
    glo = [f for k, f in S.R.items() if k.startswith("GLO")]
    P = S.R[prop_id]
    hist = {}
    for k, x in re.findall(r"\bpre(\d+)_(\w+)", str(P)):
        hist[x] = max(hist.get(x, 0), int(k))
    regs = [cur for _, cur, _ in mach.values()] + [S.resolve(f"pre{k}_{x}") for x, d in hist.items() for k in range(1, d + 1)]
    sorts = [IntSort() if r.sort() == IntSort() else BoolSort() for r in regs]
    Inv = Function("Inv", *sorts, BoolSort())
    Bad = Function("Bad", BoolSort())
    # primed copies
    prime = {str(r): (Int(str(r) + "_p") if r.sort() == IntSort() else Bool(str(r) + "_p")) for r in regs}
    nxt_of = {str(cur): nxt for _, cur, nxt in mach.values()}
    upd = []
    for r in regs:
        n = str(r)
        if n in nxt_of:
            upd.append(prime[n] == nxt_of[n])
        else:
            k, x = re.match(r"pre(\d+)_(\w+)", n).groups()
            src = S.resolve(x) if k == "1" else S.resolve(f"pre{int(k) - 1}_{x}")
            upd.append(prime[n] == src)
    step = And(S.domain, *rels, *glo)
    fp = Fixedpoint(); fp.set(engine="spacer")
    try:
        fp.set("spacer.random_seed", seed)
    except Exception:
        pass
    fp.register_relation(Inv, Bad)
    allv = {}
    for f in [step, P] + upd + regs:
        for v in _consts(f):
            allv[str(v)] = v
    fp.declare_var(*allv.values())
    init = []
    for r in regs:
        n = str(r)
        if n in nxt_of:
            m = next(m for m, (_, c, _) in mach.items() if str(c) == n)
            enum = mach[m][0]
            init.append(r == S.enums[enum].index(ir["machines"][m]["init"]))
        else:
            init.append(r == BoolVal(False))
    fp.rule(Inv(*regs), And(*init))
    fp.rule(Inv(*[prime[str(r)] for r in regs]), And(Inv(*regs), step, *upd))
    fp.rule(Bad(), And(Inv(*regs), step, Not(P)))
    r = fp.query(Bad())
    out = dict(result="proved" if str(r) == "unsat" else ("counterexample" if str(r) == "sat" else "inconclusive"),
               engine="IC3/PDR (z3 Spacer)")
    if str(r) == "unsat":
        from z3 import Var, substitute_vars
        lem = fp.get_cover_delta(-1, Inv)
        inv = substitute_vars(lem, *reversed(regs)) if False else substitute_vars(lem, *regs)
        out["invariant"] = str(simplify(inv))
        out["invariant_expr"] = inv
        out["registers"] = [str(r) for r in regs]
        # minimise: drop clauses while the remainder is still an inductive invariant that implies P
        from z3 import is_and as _isand, Solver, unsat as _unsat
        cls = list(inv.children()) if _isand(inv) else [inv]
        out["n_clauses_found"] = len(cls)
        init_f = And(*init)
        primed = lambda f: substitute(f, *[(r, prime[str(r)]) for r in regs])
        def ok(C):
            I = And(*C) if C else BoolVal(True)
            for f in (Implies(init_f, I), Implies(And(I, step, *upd), primed(I)), Implies(And(I, step), P)):
                s_ = Solver(); s_.add(Not(f))
                if s_.check() != _unsat:
                    return False
            return True
        assert ok(cls), "invariant returned by Spacer failed the inductiveness check"
        keep = list(cls)
        for c in list(cls):
            trial = [x for x in keep if not x.eq(c)]
            if ok(trial):
                keep = trial
        out["invariant_min_expr"] = And(*keep) if keep else BoolVal(True)
        out["n_clauses_min"] = len(keep)
    return out


def _consts(f):
    from logic_engine import free_consts
    return free_consts(f).values()


def _const(S, n):
    return S.vars.get(n) or (Int(n) if n.endswith("_p") is False and n in S.vtype and S.vtype[n] != "Boolean" else Bool(n))
