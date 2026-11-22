#!/usr/bin/env python3
"""Validation of the FRET-to-SysML translation against FRET's own Lustre code.

For every requirement, FRET generates a CoCoSpec (Lustre) expression ('CoCoSpecCode') over its library of temporal
operators (H, SI, OT, YtoPre, ZtoPre, preReal, ...; fret-electron/support/CommonTemplates/LibraryOfOperators.ejs and
DelayOperators.ejs). This script evaluates that expression on the unrolled trace with the Lustre definitions of the
library, using its own tokenizer and parser (nothing is shared with fret2sysml.py, which reads the 'ptExpanded'
formula instead), and proves with Z3 that, on every trace of N+1 steps and at every step t <= N,

    the SysML requirement has held at steps 0..t     <->     FRET's Lustre expression is true at t,

with the monitor attributes of the SysML model constrained by their glossary axioms. A difference would be returned
as a trace. The check is bounded by N; with N larger than every time bound of the requirements (14 ticks here), each
register chain and window of the translation is exercised at its full length.

    python3 experiments/third_party/validate_translation.py FRET.json MODEL.sysml N [OUT.json]

A sensitivity check is recorded with the result: the threshold 'kgs <= 20.0' is changed to 'kgs <= 21.0' in a copy of
the model, and the requirements that read it must then differ from FRET's code.
"""
import json, os, re, sys, time
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import (Solver, And, Or, Not, Implies, If, BoolVal, RealVal, IntVal, Int, Xor, sat, is_bool)
from semantics import compile_model
import unroll

TOK = re.compile(r"\s*(=>|<=|>=|<>|[()=<>+\-*/,]|[A-Za-z_]\w*|\d+\.\d*|\d+)")


def lex(s):
    out, i, s = [], 0, s.strip()
    while i < len(s):
        m = TOK.match(s, i)
        if not m:
            raise ValueError(f"cannot read {s[i:i + 20]!r}")
        out.append(m.group(1)); i = m.end()
        while i < len(s) and s[i].isspace():
            i += 1
    return out


class Parser:
    """Lustre expressions as FRET prints them: =>, or, xor, and, not, comparisons, + - * /, calls, literals."""
    def __init__(self, s):
        self.t, self.i = lex(s), 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        t = self.peek()
        if x is not None and t != x:
            raise ValueError(f"expected {x}, got {t}")
        self.i += 1
        return t

    def top(self):
        e = self.imp()
        assert self.peek() is None, self.t[self.i:]
        return e

    def imp(self):
        a = self.orr()
        if self.peek() == "=>":
            self.eat(); return ("=>", a, self.imp())
        return a

    def orr(self):
        a = self.andd()
        while self.peek() in ("or", "xor"):
            a = (self.eat(), a, self.andd())
        return a

    def andd(self):
        a = self.nott()
        while self.peek() == "and":
            self.eat(); a = ("and", a, self.nott())
        return a

    def nott(self):
        if self.peek() == "not":
            self.eat(); return ("not", self.nott())
        return self.cmp()

    def cmp(self):
        a = self.add()
        if self.peek() in ("=", "<>", "<", "<=", ">", ">="):
            return (self.eat(), a, self.add())
        return a

    def add(self):
        a = self.mul()
        while self.peek() in ("+", "-"):
            a = (self.eat(), a, self.mul())
        return a

    def mul(self):
        a = self.una()
        while self.peek() in ("*", "/"):
            a = (self.eat(), a, self.una())
        return a

    def una(self):
        if self.peek() == "-":
            self.eat(); return ("neg", self.una())
        return self.atom()

    def atom(self):
        t = self.eat()
        if t == "(":
            e = self.imp(); self.eat(")"); return e
        if re.fullmatch(r"\d+\.\d*", t):
            return ("real", t)
        if re.fullmatch(r"\d+", t):
            return ("int", int(t))
        if t in ("true", "false"):
            return ("bool", t == "true")
        if self.peek() == "(":
            self.eat(); args = [self.imp()]
            while self.peek() == ",":
                self.eat(); args.append(self.imp())
            self.eat(")")
            return ("call", t, args)
        return ("id", t)


class Lustre:
    """Value of a FRET Lustre expression at step t of an unrolling, by the library's Lustre definitions."""
    def __init__(self, U, enum_lits):
        self.U, self.lits, self.memo = U, enum_lits, {}

    def ev(self, e, t):
        key = (id(e), t)
        if key not in self.memo:
            self.memo[key] = self._ev(e, t)
        return self.memo[key]

    def _ev(self, e, t):
        op = e[0]
        if op == "bool":
            return BoolVal(e[1])
        if op == "real":
            return RealVal(e[1])
        if op == "int":
            return IntVal(e[1])
        if op == "id":
            n = e[1]
            if n in self.lits:
                return IntVal(self.lits[n])
            if n == "FTP":            # FTP = true -> false
                return BoolVal(t == 0)
            return self.U.var(n, t)
        if op == "not":
            return Not(self.ev(e[1], t))
        if op == "neg":
            return -self.ev(e[1], t)
        if op in ("and", "or", "=>", "xor"):
            a, b = self.ev(e[1], t), self.ev(e[2], t)
            return {"and": And, "or": Or, "=>": Implies, "xor": Xor}[op](a, b)
        if op in ("=", "<>", "<", "<=", ">", ">=", "+", "-", "*", "/"):
            a, b = self.ev(e[1], t), self.ev(e[2], t)
            return {"=": lambda: a == b, "<>": lambda: a != b, "<": lambda: a < b, "<=": lambda: a <= b,
                    ">": lambda: a > b, ">=": lambda: a >= b, "+": lambda: a + b, "-": lambda: a - b,
                    "*": lambda: a * b, "/": lambda: a / b}[op]()
        assert op == "call", e
        f, A = e[1], e[2]
        x = lambda i, u=t: self.ev(A[i], u)
        if f == "H":           # Y = X -> (X and (pre Y))
            return x(0) if t == 0 else And(x(0), self.ev(e, t - 1))
        if f == "O":           # Y = X or (false -> pre Y)
            return x(0) if t == 0 else Or(x(0), self.ev(e, t - 1))
        if f == "SI":          # Z = Y and (X or (false -> pre Z))
            return And(x(1), x(0) if t == 0 else Or(x(0), self.ev(e, t - 1)))
        if f == "S":           # Z = X or (Y and (false -> pre Z))
            return x(0) if t == 0 else Or(x(0), And(x(1), self.ev(e, t - 1)))
        if f == "YtoPre":      # false -> pre X
            return BoolVal(False) if t == 0 else x(0, t - 1)
        if f == "ZtoPre":      # true -> pre X
            return BoolVal(True) if t == 0 else x(0, t - 1)
        if f in ("preReal", "preBool", "preInt"):   # InitialValue -> pre X
            return x(0) if t == 0 else x(1, t - 1)
        if f in ("absReal", "absInt"):
            v = x(0); return If(v >= 0, v, -v)
        if f == "OT":          # D = delay(X, R); Y = OTlore(L - R, D)
            const = lambda a: (a[1] if a[0] == "int" else {"+": int.__add__, "-": int.__sub__, "*": int.__mul__}[a[0]](
                const(a[1]), const(a[2])))
            L, R = const(A[0]), const(A[1])
            N = L - R

            def D(u):           # delay: X_j = false -> pre X_{j-1}
                return x(2, u - R) if u - R >= 0 else BoolVal(False)

            def C(u):           # C = if X then 0 else (-1 -> pre C + (if pre C < 0 then 0 else 1))
                k = ("C", id(e), u)
                if k not in self.memo:
                    if u == 0:
                        self.memo[k] = If(D(0), IntVal(0), IntVal(-1))
                    else:
                        p = C(u - 1)
                        self.memo[k] = If(D(u), IntVal(0), p + If(p < 0, IntVal(0), IntVal(1)))
                return self.memo[k]
            c = C(t)
            return And(c >= 0, c <= N)
        raise ValueError(f"operator {f} not in FRET's library subset handled here")


def main(fret, model, N, out):
    T0 = time.time()
    S = compile_model(model)
    lits = {}
    for E in S.enums.values():
        lits.update({l: i for i, l in enumerate(E)})
    reqs = {r["reqid"]: r for r in json.load(open(fret))["requirements"]}
    mon = [k for k in S.R if k.startswith("GLO-MON")]
    keys = [k for k in S.R if not k.startswith("GLO")]
    U = unroll.Unrolling(S, N)
    ctx = [U.reqs(mon, t) for t in range(N + 1)]
    res, bad = {}, []
    for k in keys:
        code = reqs[k]["semantics"]["CoCoSpecCode"]
        ast = Parser(code).top()
        Lu = Lustre(U, lits)
        diff = []
        held = BoolVal(True)
        for t in range(N + 1):
            held = And(held, U.step(S.R[k], t))
            diff.append(Xor(held, Lu.ev(ast, t)))
        s = Solver(); s.add(*ctx, Or(*diff))
        r = s.check()
        res[k] = "equivalent" if r != sat else "differs"
        if r == sat:
            bad.append(k)
    rep = dict(fret=os.path.basename(fret), model=os.path.relpath(model, ROOT), steps=N + 1,
               requirements=len(keys), equivalent=sum(v == "equivalent" for v in res.values()), differs=bad,
               seconds=round(time.time() - T0, 1), per_requirement=res)
    if out and "kgs <= 20.0" in open(model).read():
        import tempfile
        t = tempfile.NamedTemporaryFile("w", suffix=".sysml", delete=False)
        t.write(open(model).read().replace("kgs <= 20.0", "kgs <= 21.0")); t.close()
        rep["perturbation"] = dict(change="kgs <= 20.0 -> kgs <= 21.0",
                                   detected_in=main(fret, t.name, N, None)["differs"])
        os.unlink(t.name)
    if out:
        json.dump(rep, open(out, "w"), indent=1)
    print({a: b for a, b in rep.items() if a != "per_requirement"})
    return rep


if __name__ == "__main__":
    a = sys.argv[1:]
    main(a[0], a[1], int(a[2]), a[3] if len(a) > 3 else None)
