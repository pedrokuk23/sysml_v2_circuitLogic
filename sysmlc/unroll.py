#!/usr/bin/env python3
"""Unrolling of a requirement set over time (bounded model checking on the circuit).

The compiled requirements are combinational constraints over the current values of the signals, their previous values
(pre<k>_x) and the first-time-point flag (ftp). Copying the circuit once per step and wiring pre<k>_x of step t to x of
step t-k gives the bounded unrolling used by hardware model checkers. On it:

  * trace(S, keys, N, extra)      a trace of N+1 steps on which every requirement in keys holds at every step;
  * earliest(S, keys, N, goal)    the first step at which goal can hold on such a trace;
  * lasso(S, keys, L)             a trace of L+1 steps whose last step repeats an earlier one: an infinite trace,
                                  hence consistency of the requirements over infinite time (for a set without inputs,
                                  this is realizability);
  * equivalent_over(S, a, b, N)   whether two requirements accept the same traces of up to N+1 steps (a miter on the
                                  unrolling);
  * reachable_conflicts / reachable_holes for requirements of the form  a -> y == e : conflicts and undriven
    situations at step t on traces where every requirement held before t.

    pre<k>_x at a step t < k is a fresh, unconstrained value; well-formed past-time requirements guard it with ftp.

Every query has three outcomes, SAT, UNSAT and UNKNOWN, and the functions report them as such: an absence (no trace,
no lasso, no difference) is concluded only from UNSAT, and an UNKNOWN answer is reported as inconclusive, with the
solver's reason, never as a conclusion.
"""
import re
from z3 import (Solver, And, Or, Not, Bool, Real, Int, BoolVal, substitute, sat, unsat, is_bool, is_int, is_real,
                is_implies, is_eq, is_const)


SAT, UNSAT, UNKNOWN = "sat", "unsat", "unknown"


def check(s):
    """Status of a solver query: ('sat'|'unsat'|'unknown', reason or None)."""
    r = s.check()
    if r == sat:
        return SAT, None
    if r == unsat:
        return UNSAT, None
    return UNKNOWN, s.reason_unknown()


class Inconclusive(Exception):
    """Raised by callers that need a definite answer when the solver returned UNKNOWN."""


def _mk(v, name):
    return Bool(name) if is_bool(v) else Int(name) if is_int(v) else Real(name)


class Unrolling:
    def __init__(self, S, N):
        self.S, self.N = S, N
        self.base = {n: v for n, v in S.vars.items()}
        self.at = [dict() for _ in range(N + 1)]
        self.fresh = {}
        plain = [n for n in self.base if not re.match(r"pre\d+_", n) and n != "ftp"]
        for t in range(N + 1):
            for n in plain:
                self.at[t][n] = _mk(self.base[n], f"{n}@{t}")

    def var(self, n, t):
        if n == "ftp":
            return BoolVal(t == 0)
        m = re.match(r"pre(\d+)_(\w+)$", n)
        if m:
            k, x = int(m.group(1)), m.group(2)
            if t - k >= 0 and x in self.at[t - k]:
                return self.at[t - k][x]
            key = (n, t)
            if key not in self.fresh:
                self.fresh[key] = _mk(self.base[n], f"{n}@{t}")
            return self.fresh[key]
        return self.at[t][n]

    def step(self, f, t):
        pairs = [(v, self.var(n, t)) for n, v in self.base.items()]
        return substitute(f, *pairs)

    def reqs(self, keys, t):
        return And(*[self.step(self.S.R[k], t) for k in keys], self.step(self.S.domain, t))


def _model_trace(U, m, names, T):
    out = []
    for t in range(T + 1):
        row = {}
        for n in names:
            v = m.eval(U.var(n, t), model_completion=True)
            row[n] = str(v)
        out.append(row)
    return out


def trace(S, keys, N, extra=None, show=()):
    U = Unrolling(S, N)
    s = Solver()
    for t in range(N + 1):
        s.add(U.reqs(keys, t))
    if extra is not None:
        s.add(extra(U))
    st, why = check(s)
    if st == SAT:
        return st, _model_trace(U, s.model(), show, N)
    return st, (dict(reason=why) if st == UNKNOWN else None)


def earliest(S, keys, N, goal, show=()):
    """First t <= N such that some trace satisfying keys at steps 0..t has goal at t.
    Returns (status, t, trace): ('sat', t, trace) when found and every earlier step was UNSAT; ('unsat', None, None)
    when every step up to N is UNSAT; ('unknown', t, reason) at the first step whose answer is UNKNOWN."""
    for t in range(N + 1):
        U = Unrolling(S, t)
        s = Solver()
        for u in range(t + 1):
            s.add(U.reqs(keys, u))
        s.add(goal(U, t))
        st, why = check(s)
        if st == SAT:
            return SAT, t, _model_trace(U, s.model(), show, t)
        if st == UNKNOWN:
            return UNKNOWN, t, why
    return UNSAT, None, None


def lasso(S, keys, L, show=()):
    """A trace of L+1 steps satisfying keys whose step L equals some step j in 1..L-1 on every plain signal and
    monitor, so that it can be repeated forever."""
    U = Unrolling(S, L)
    s = Solver()
    for t in range(L + 1):
        s.add(U.reqs(keys, t))
    plain = list(U.at[0])
    s.add(Or(*[And(*[U.at[L][n] == U.at[j][n] for n in plain]) for j in range(1, L)]))
    st, why = check(s)
    if st == SAT:
        return st, _model_trace(U, s.model(), show, L)
    return st, (dict(reason=why) if st == UNKNOWN else None)


def equivalent_over(S, a, b, N, context=()):
    """Do requirements a and b accept the same traces of up to N+1 steps (under the context requirements, e.g. the
    monitor definitions)?  Returns ('equivalent', None) only when every query is UNSAT, ('differs', detail) with the
    first step of a difference, or ('unknown', detail) when a query is inconclusive before any difference is found."""
    for t in range(N + 1):
        U = Unrolling(S, t)
        ctx = [U.reqs(context, u) for u in range(t + 1)]
        for x, y in ((a, b), (b, a)):
            s = Solver()
            s.add(*ctx)
            s.add(*[U.step(S.R[x], u) for u in range(t + 1)])
            s.add(*[U.step(S.R[y], u) for u in range(t)])
            s.add(Not(U.step(S.R[y], t)))
            st, why = check(s)
            if st == SAT:
                return "differs", dict(step=t, holds=x, fails=y)
            if st == UNKNOWN:
                return UNKNOWN, dict(step=t, holds=x, fails=y, reason=why)
    return "equivalent", None


def _antecedent_consequent(f):
    if is_implies(f) and is_eq(f.arg(1)):
        return f.arg(0), f.arg(1)
    return None


def reachable_conflicts(S, keys, group, N, context=None):
    """Pairs of requirements of 'group' (a -> y == e) whose antecedents hold together at some step t <= N, with
    different values demanded, on a trace where every requirement of 'keys' held at the steps before t.
    Returns (conflicts, inconclusive): the second list holds the pair/step queries whose answer was UNKNOWN."""
    context = keys if context is None else context
    out, unk = [], []
    g = [(k, _antecedent_consequent(S.R[k])) for k in group]
    for t in range(1, N + 1):
        U = Unrolling(S, t)
        pre = [U.reqs(context, u) for u in range(t)]
        dom = U.step(S.domain, t)
        for i in range(len(g)):
            for j in range(i + 1, len(g)):
                (ki, (ai, ci)), (kj, (aj, cj)) = g[i], g[j]
                s = Solver()
                s.add(*pre, dom, U.step(ai, t), U.step(aj, t))
                s.add(*[U.step(S.R[k], t) for k in context if k.startswith("GLO")])
                s.add(Not(And(U.step(ci, t), U.step(cj, t))))
                st, why = check(s)
                if st == SAT and not any(o["requirements"] == [ki, kj] for o in out):
                    out.append(dict(requirements=[ki, kj], step=t))
                elif st == UNKNOWN:
                    unk.append(dict(requirements=[ki, kj], step=t, reason=why))
    return out, unk


def reachable_holes(S, keys, group, N, show=()):
    """Steps t <= N at which, on some trace where every requirement held before t (and the glossary at t), no
    antecedent of 'group' holds: the output is undriven there.  Returns (holes, inconclusive steps)."""
    out, unk = [], []
    g = [_antecedent_consequent(S.R[k])[0] for k in group]
    for t in range(1, N + 1):
        U = Unrolling(S, t)
        s = Solver()
        s.add(*[U.reqs(keys, u) for u in range(t)], U.step(S.domain, t))
        s.add(*[U.step(S.R[k], t) for k in keys if k.startswith("GLO")])
        s.add(*[Not(U.step(a, t)) for a in g])
        st, why = check(s)
        if st == SAT:
            out.append(dict(step=t, example=_model_trace(U, s.model(), show, t)))
        elif st == UNKNOWN:
            unk.append(dict(step=t, reason=why))
    return out, unk
