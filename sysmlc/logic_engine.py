#!/usr/bin/env python3
"""Logic engine for requirements, over Booleans, enumerations and real arithmetic (z3).

Each operation is one theorem of logic used as an engineering check:
  refines      deduction theorem: children, A |- parent  iff  A & children & ~parent is UNSAT
  conflicts    unsatisfiable cores: input situations where no output satisfies a set of requirements
  redundant    entailment by the others (A & others & ~r UNSAT)
  vacuous      antecedent unsatisfiable under A
  dead_parts   sub-formulas that are valid or unsatisfiable under A (simplification by equivalence)
  coverage     case-split completeness (A & ~(c1|...|cn)) and overlaps (A & ci & cj)
  abduce       weakest missing hypothesis over a chosen vocabulary V: W(V) = forall(others). (A & children -> parent)
  interpolate  Craig interpolants between two subsystems: strongest = exists(local_A). A ; weakest = forall(local_B). ~B
  region       quantifier elimination: the input region (formula over inputs) where a property holds
Quantifier elimination uses z3's qe2 (works for nonlinear real arithmetic) and falls back to qe.
"""
from z3 import (Solver, sat, unsat, unknown, And, Or, Not, Implies, ForAll, Exists, Tactic, BoolVal, simplify,
                is_bool, is_quantifier, is_and, is_or, is_not, is_implies, is_const, is_true, is_false, substitute, Z3_OP_UNINTERPRETED)
import itertools


def is_sat(*fs):
    s = Solver(); s.add(*fs)
    r = s.check()
    return (r == sat), (s.model() if r == sat else None)


def valid(f, A=BoolVal(True)):
    """Validity of f under A. An 'unknown' answer of the solver counts as not valid (no proof)."""
    s = Solver(); s.add(A, Not(f))
    r = s.check()
    return (r == unsat), (s.model() if r == sat else None)


def has_quantifier(e):
    if is_quantifier(e):
        return True
    return any(has_quantifier(c) for c in e.children())


def qe(f):
    """Quantifier elimination. qe2 (QSAT, also nonlinear reals) is only applied to formulas whose top symbol is a
    quantifier: on a ground formula it answers satisfiability instead of returning the formula."""
    if not has_quantifier(f):
        order = ()
    elif is_quantifier(f):
        order = ("qe2", "qe")
    else:
        order = ("qe", "qe2")
    e = f
    for t in order:
        try:
            e = Tactic(t)(f).as_expr()
            break
        except Exception:
            continue
    return simplify(Tactic("ctx-solver-simplify")(e).as_expr())


def free_consts(f):
    out, seen = {}, set()
    def walk(e):
        if e.get_id() in seen:
            return
        seen.add(e.get_id())
        if is_const(e) and e.decl().kind() == Z3_OP_UNINTERPRETED:
            out[str(e)] = e
        for c in e.children():
            walk(c)
    walk(f)
    return out


# ---------------------------------------------------------------- deduction theorem
def refines(parent, children, A=BoolVal(True), inputs=None):
    hyp = And(A, *children)
    s_ = Solver(); s_.add(hyp, Not(parent)); r_ = s_.check()
    ok, m = (r_ != unsat), (s_.model() if r_ == sat else None)
    res = dict(valid=not ok, children_consistent=is_sat(hyp)[0])
    if r_ == unknown:
        res["solver"] = "unknown"
        return res
    if ok:
        res["counterexample"] = {str(d): str(m[d]) for d in m.decls()}
        if inputs is not None:
            loc = [v for k, v in free_consts(And(hyp, Not(parent))).items() if k not in {str(i) for i in inputs}]
            res["counterexample_region"] = str(qe(Exists(loc, And(hyp, Not(parent))) if loc else And(hyp, Not(parent))))
    return res


# ---------------------------------------------------------------- unsat cores on situations
def conflicts(reqs, A, inputs, max_size=3):
    """reqs: id -> formula. A situation (valuation of inputs) is in conflict for a set S if no assignment of the
    remaining variables satisfies A & S. Returns minimal sets (by size) with the input region where they clash."""
    ids = list(reqs)
    names = {str(i) for i in inputs}
    found = []
    for k in range(2, max_size + 1):
        for S in itertools.combinations(ids, k):
            if any(set(F) <= set(S) for F, _ in found):
                continue                                  # not minimal
            body = And(A, *[reqs[i] for i in S])
            others = [v for n, v in free_consts(body).items() if n not in names]
            clash = And(A_inputs(A, inputs), Not(Exists(others, body)) if others else Not(body))
            ok, m = is_sat(clash)
            if ok:
                found.append((S, str(qe(clash))))
    return [dict(requirements=list(S), region=r) for S, r in found]


def A_inputs(A, inputs):
    """The part of the assumptions that speaks only about inputs (admissible situations)."""
    names = {str(i) for i in inputs}
    others = [v for n, v in free_consts(A).items() if n not in names]
    return qe(Exists(others, A)) if others else A


def redundant(reqs, A):
    out = []
    for k in reqs:
        ok, _ = valid(reqs[k], And(A, *[reqs[j] for j in reqs if j != k]))
        if ok:
            out.append(k)
    return out


def vacuous(reqs, A):
    out = []
    for k, f in reqs.items():
        if is_implies(f) and not is_sat(A, f.arg(0))[0]:
            out.append(k)
    return out


# ---------------------------------------------------------------- simplification by equivalence
def dead_parts(f, A=BoolVal(True)):
    """Non-atomic Boolean sub-formulas that are valid (≡ true) or unsatisfiable (≡ false) under A."""
    out, seen = [], set()
    def walk(e):
        if e.get_id() in seen:
            return
        seen.add(e.get_id())
        if is_bool(e) and (is_and(e) or is_or(e) or is_not(e) or is_implies(e)):
            if valid(e, A)[0]:
                out.append((str(e), "always true"))
            elif not is_sat(A, e)[0]:
                out.append((str(e), "always false"))
        for c in e.children():
            walk(c)
    walk(f)
    return out


def coverage(cases, A=BoolVal(True), inputs=None):
    """cases: id -> condition. Holes = A & none of the conditions; overlaps = A & ci & cj."""
    hole = And(A, Not(Or(*cases.values())))
    ok, m = is_sat(hole)
    res = dict(complete=not ok)
    if ok:
        res["hole_region"] = str(qe(hole))
        res["hole_example"] = {str(d): str(m[d]) for d in m.decls()}
    ov = []
    for a, b in itertools.combinations(cases, 2):
        o = And(A, cases[a], cases[b])
        if is_sat(o)[0]:
            ov.append(dict(cases=[a, b], region=str(qe(o))))
    res["overlaps"] = ov
    return res


# ---------------------------------------------------------------- abduction and interpolation
def abduce(parent, children, A, vocabulary):
    """Weakest W over `vocabulary` with  A & children & W |- parent.  W = forall(others).(A & children -> parent)."""
    body = Implies(And(A, *children), parent)
    names = {str(v) for v in vocabulary}
    others = [v for n, v in free_consts(body).items() if n not in names]
    W = qe(ForAll(others, body)) if others else simplify(body)
    consistent = is_sat(A, *children, W)[0]
    return dict(W=str(W), W_expr=W, consistent_with_children=consistent)


def interpolate(fa, fb, shared):
    """fa & fb UNSAT. Strongest interpolant exists(local_a).fa ; weakest forall(local_b).~fb; both over `shared`."""
    assert not is_sat(fa, fb)[0], "A & B must be unsatisfiable"
    names = {str(v) for v in shared}
    la = [v for n, v in free_consts(fa).items() if n not in names]
    lb = [v for n, v in free_consts(fb).items() if n not in names]
    strongest = qe(Exists(la, fa)) if la else fa
    weakest = qe(ForAll(lb, Not(fb))) if lb else simplify(Not(fb))
    return dict(strongest=str(strongest), weakest=str(weakest), strongest_expr=strongest, weakest_expr=weakest)


def region(f, keep):
    names = {str(v) for v in keep}
    loc = [v for n, v in free_consts(f).items() if n not in names]
    return qe(Exists(loc, f)) if loc else qe(f)


def finite_region(f, bools, enums):
    """Readable region of a formula over finite inputs: for each combination of enumeration values where f is
    satisfiable, the minimal DNF over the Boolean inputs. bools: list of z3 Bools; enums: {z3 Int: {value: label}}."""
    from sympy import symbols as ssym
    from sympy.logic import SOPform
    names = [str(b) for b in bools]
    S = ssym(" ".join(names)); S = S if isinstance(S, tuple) else (S,)
    parts = []
    for combo in itertools.product(*[list(d.items()) for d in enums.values()]):
        sub = [v == val for v, (val, lab) in zip(enums, combo)]
        if not is_sat(f, *sub)[0]:
            continue
        ones = []
        for bits in itertools.product([0, 1], repeat=len(bools)):
            if is_sat(f, *sub, *[b if x else Not(b) for b, x in zip(bools, bits)])[0]:
                ones.append(list(bits))
        dnf = SOPform(list(S), ones) if len(ones) < 2 ** len(bools) else "qualquer"
        lab = ", ".join(f"{v}={l}" for v, (val, l) in zip(enums, combo))
        parts.append(f"[{lab}] " + str(dnf).replace("~", "¬").replace("&", "∧").replace("|", "∨"))
    return parts or ["nenhuma"]
