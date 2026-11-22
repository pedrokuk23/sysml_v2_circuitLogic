#!/usr/bin/env python3
"""Translate a FRET project (requirements with their past-time metric LTL semantics, 'ptExpanded') into a SysML v2
model in the sysmlc subset.

Every temporal operator becomes a MONITOR: a Boolean attribute defined by a one-step glossary axiom over its previous
value (pre1_) and the first-time-point flag 'ftp', i.e. a register, which is how a past-time formula is built as a
sequential circuit:

    Y p      -> (not ftp and pre1_a)                 a == p   (a fresh attribute when p is not a name)
    Z p      -> (ftp or pre1_a)
    H p      -> m,  m == (p and (ftp or pre1_m))
    O p      -> m,  m == (p or (not ftp and pre1_m))
    p S q    -> m,  m == (q or (p and not ftp and pre1_m))
    O[0,n] p -> o_n, o_0 == p, o_j == (p or (not ftp and pre1_o_{j-1}))
    preReal(i, x) / preBool(i, x) -> (if ftp ? i else pre1_x);   absReal(e) -> (if e >= 0 ? e else -e);   FTP -> ftp

A requirement 'H phi' becomes 'require constraint { phi }' (it must hold at every step). One simplification is applied
and recorded: in  Y(...) -> (q | Z FALSE)  the disjunct  Z FALSE  (true only at the first step) is dropped, because
the antecedent Y(...) is false at the first step; this gives the  a -> y == e  form that the output-group analysis
reads. The original text, the FRETish sentence and the ptExpanded formula are kept in each requirement's doc.

    python3 experiments/third_party/fret2sysml.py FRET.json OUT.sysml [--exclude ID,ID] [--package NAME]
"""
import json, re, sys

TOK = re.compile(r"\s*(<->|->|<=|>=|!=|\[|\]|[()&|!=<>+\-*/,]|[A-Za-z_]\w*|\d+\.\d+|\d+)")


def tokens(s):
    s = s.strip()
    out, i = [], 0
    while i < len(s):
        m = TOK.match(s, i)
        if not m:
            raise ValueError(f"cannot tokenize at {s[i:i+20]!r}")
        out.append(m.group(1)); i = m.end()
    return out


class P:
    """Pratt parser for FRET's pmLTL (ptExpanded)."""
    def __init__(self, s):
        self.t, self.i = tokens(s), 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def take(self, x=None):
        t = self.peek()
        if x is not None and t != x:
            raise ValueError(f"expected {x!r}, got {t!r} in {' '.join(self.t)}")
        self.i += 1
        return t

    def parse(self):
        e = self.iff()
        if self.peek() is not None:
            raise ValueError(f"trailing {self.peek()!r}")
        return e

    def iff(self):
        a = self.imp()
        while self.peek() == "<->":
            self.take(); a = ("<->", a, self.imp())
        return a

    def imp(self):
        a = self.orr()
        if self.peek() == "->":
            self.take(); return ("->", a, self.imp())
        return a

    def orr(self):
        a = self.since()
        while self.peek() in ("|", "xor"):
            op = self.take(); a = (op, a, self.since())
        return a

    def since(self):
        a = self.andd()
        while self.peek() == "S":
            self.take(); a = ("S", a, self.andd())
        return a

    def andd(self):
        a = self.cmp()
        while self.peek() == "&":
            self.take(); a = ("&", a, self.cmp())
        return a

    def cmp(self):
        a = self.add()
        if self.peek() in ("=", "!=", "<", "<=", ">", ">="):
            op = self.take(); return (op, a, self.add())
        return a

    def add(self):
        a = self.mul()
        while self.peek() in ("+", "-"):
            op = self.take(); a = (op, a, self.mul())
        return a

    def mul(self):
        a = self.un()
        while self.peek() in ("*", "/"):
            op = self.take(); a = (op, a, self.un())
        return a

    def un(self):
        t = self.peek()
        if t == "!":
            self.take(); return ("!", self.un())
        if t == "-":
            self.take(); return ("neg", self.un())
        if t in ("H", "O", "Y", "Z"):
            self.take()
            if self.peek() == "[":
                self.take(); lo = self.take(); self.take(","); hi = self.take(); self.take("]")
                return (t + "[]", int(lo), int(hi), self.un())
            return (t, self.un())
        return self.atom()

    def atom(self):
        t = self.take()
        if t == "(":
            e = self.iff(); self.take(")"); return e
        if re.match(r"\d", t):
            return ("num", t)
        if t in ("TRUE", "FALSE"):
            return ("bool", t == "TRUE")
        if self.peek() == "(" and t in ("absReal", "preReal", "preBool", "preInt"):
            self.take("(")
            args = [self.iff()]
            while self.peek() == ",":
                self.take(); args.append(self.iff())
            self.take(")")
            return ("call", t, args)
        return ("var", t)


class Gen:
    def __init__(self, vars_, enum_name, enum_lits):
        self.vars = vars_                 # name -> (kind, type)   kind in Input/Output/Internal
        self.enum, self.lits = enum_name, enum_lits
        self.mon = []                     # (name, expr text, deps)
        self.cache = {}
        self.n = 0
        self.used = set()

    def fresh(self, base):
        self.n += 1
        return f"{base}{self.n}"

    def name_of(self, e):
        """A Boolean attribute equal to e (e itself when e is a Boolean variable)."""
        if e[0] == "var" and e[1] in self.vars and self.vars[e[1]][1] == "Boolean":
            self.used.add(e[1])
            return e[1]
        key = repr(e)
        if key in self.cache:
            return self.cache[key]
        a = self.fresh("a")
        self.cache[key] = a
        self.mon.append((a, self.x(e)))
        return a

    def x(self, e):
        k = e[0]
        if k == "num":
            return e[1]
        if k == "bool":
            return "true" if e[1] else "false"
        if k == "var":
            v = e[1]
            if v == "FTP":
                return "ftp"
            if v in self.lits:
                return f"{self.enum}::{v}"
            self.used.add(v)
            return v
        if k == "!":
            return f"(not {self.x(e[1])})"
        if k == "neg":
            return f"(- {self.x(e[1])})"
        if k in ("&", "|", "->", "<->", "xor"):
            op = {"&": "and", "|": "or", "->": "implies", "<->": "==", "xor": "xor"}[k]
            if k == "->" and e[2][0] == "|" and e[2][2] in (("Z", ("bool", False)), ("!", ("Y", ("bool", True)))) \
                    and self.starts_with_Y(e[1]):
                return f"({self.x(e[1])} implies {self.x(e[2][1])})"
            return f"({self.x(e[1])} {op} {self.x(e[2])})"
        if k in ("=", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/"):
            op = "==" if k == "=" else k
            return f"({self.x(e[1])} {op} {self.x(e[2])})"
        if k == "Y":
            if e[1] == ("bool", True):
                return "(not ftp)"
            return f"(not ftp and pre1_{self.name_of(e[1])})"
        if k == "Z":
            if e[1] == ("bool", False):
                return "ftp"
            return f"(ftp or pre1_{self.name_of(e[1])})"
        if k in ("H", "O"):
            key = repr(e)
            if key in self.cache:
                return self.cache[key]
            m = self.fresh("h" if k == "H" else "o")
            self.cache[key] = m
            p = self.x(e[1])
            self.mon.append((m, f"({p} and (ftp or pre1_{m}))" if k == "H" else f"({p} or (not ftp and pre1_{m}))"))
            return m
        if k == "S":
            key = repr(e)
            if key in self.cache:
                return self.cache[key]
            m = self.fresh("s")
            self.cache[key] = m
            self.mon.append((m, f"({self.x(e[2])} or ({self.x(e[1])} and not ftp and pre1_{m}))"))
            return m
        if k == "O[]":
            lo, hi, p = e[1], e[2], e[3]
            if lo != 0:
                raise ValueError("O[a,b] with a > 0")
            key = repr(e)
            if key in self.cache:
                return self.cache[key]
            pt = self.x(p)
            prev = self.fresh("w")
            self.mon.append((prev, pt))
            for _ in range(hi):
                m = self.fresh("w")
                self.mon.append((m, f"({pt} or (not ftp and pre1_{prev}))"))
                prev = m
            self.cache[key] = prev
            return prev
        if k == "call":
            f, a = e[1], e[2]
            if f == "absReal":
                t = self.x(a[0]); return f"(if {t} >= 0 ? {t} else (- {t}))"
            if f in ("preReal", "preBool", "preInt"):
                init, v = self.x(a[0]), a[1]
                if v[0] != "var":
                    v = ("var", self.name_of(v))
                self.used.add(v[1])
                return f"(if ftp ? {init} else pre1_{v[1]})"
        raise ValueError(f"unsupported {e!r}")

    @staticmethod
    def starts_with_Y(e):
        return e[0] == "Y" or (e[0] == "&" and (Gen.starts_with_Y(e[1]) or Gen.starts_with_Y(e[2])))


def translate(fret, exclude=(), package="LPC"):
    d = json.load(open(fret))
    vars_ = {}
    enum_lits = []
    for v in d["variables"]:
        n, kind, dt = v["variable_name"], v["idType"], v["dataType"]
        if kind == "Internal" and dt == "integer" and re.fullmatch(r"\d+", (v.get("assignment") or "").strip()):
            enum_lits.append((int(v["assignment"]), n))      # named integer constants (FRET Internal) -> enumeration
            continue
        vars_[n] = (kind, {"boolean": "Boolean", "double": "Real", "integer": "Integer"}[dt])
    enum_lits = [n for _, n in sorted(enum_lits)]
    enum_name = "LiftModeKind"
    for n, (k, t) in list(vars_.items()):
        if t == "Integer" and enum_lits:
            vars_[n] = (k, enum_name)
    G = Gen(vars_, enum_name, set(enum_lits))
    reqs = []
    for r in sorted(d["requirements"], key=lambda r: r["reqid"]):
        if r["reqid"] in exclude:
            continue
        pt = r["semantics"]["ptExpanded"]
        e = P(pt).parse()
        while e[0] == "&" and e[1][0] == "H" and e[2][0] == "H":      # H a & H b  ==  H (a & b)
            e = ("H", ("&", e[1][1], e[2][1]))
        if e[0] != "H":
            raise ValueError(f"{r['reqid']}: top-level operator is not H")
        G.used = set()
        mon_before = len(G.mon)
        body = G.x(e[1])
        reqs.append(dict(id=r["reqid"], text=r["fulltext"], pt=pt, expr=body, used=set(G.used)))
    return d, vars_, enum_name, enum_lits, G, reqs


def free_names(expr):
    return set(re.findall(r"(?<![\w:])([A-Za-z_]\w*)(?![\w:])", expr)) - {"and", "or", "not", "implies", "if", "else", "xor",
                                                                           "true", "false"}


def emit(fret, out, exclude=(), package="LPC"):
    d, vars_, enum_name, enum_lits, G, reqs = translate(fret, exclude, package)
    mon_names = {m for m, _ in G.mon}
    def typ(n):
        if n == "ftp" or n in mon_names:
            return "Boolean"
        if n.startswith("pre1_"):
            return typ(n[5:])
        return vars_[n][1]
    def attrs(expr, outs):
        names = sorted(free_names(expr) - {enum_name})
        lines = []
        for n in names:
            d_ = "out" if n in outs else "in"
            lines.append(f"        {d_} attribute {n} : {typ(n)};")
        return "\n".join(lines)
    outputs = {n for n, (k, t) in vars_.items() if k == "Output"}
    L = [f"// Generated by experiments/third_party/fret2sysml.py from {fret.split('/')[-1]} (NASA FRET, Apache-2.0).",
         "// Each FRET requirement keeps its text and its past-time semantics (ptExpanded) in the doc; temporal",
         "// operators are monitors (registers) defined by glossary axioms GLO-MON-*. 'ftp' is the first time point.",
         f"package {package} {{", "    private import ScalarValues::*;", "",
         f"    enum def {enum_name} {{ " + " ".join(f"enum {l};" for l in enum_lits) + " }", ""]
    for i, (m, ex) in enumerate(G.mon, 1):
        L += [f"    requirement def <'GLO-MON-{i:03d}'> Monitor_{m} {{",
              "        subject vehicle;",
              f"        doc /* Monitor {m}: register of a past-time operator. */",
              attrs(f"{m} {ex}", {m}),
              f"        require constraint {{ {m} == {ex} }}", "    }"]
    for r in reqs:
        doc = r["text"].replace("*/", "* /")
        pt = r["pt"].replace("*/", "* /")
        L += [f"    requirement def <'{r['id']}'> {re.sub(r'[^A-Za-z0-9]', '_', r['id'])} {{",
              "        subject vehicle;",
              f"        doc /* {doc}\n           ptExpanded: {pt} */",
              attrs(r["expr"], outputs),
              f"        require constraint {{ {r['expr']} }}", "    }"]
    L.append("}")
    open(out, "w").write("\n".join(L) + "\n")
    return len(reqs), len(G.mon)


if __name__ == "__main__":
    ex = ()
    pkg = "LPC"
    a = sys.argv[1:]
    if "--exclude" in a:
        i = a.index("--exclude"); ex = tuple(a[i + 1].split(",")); del a[i:i + 2]
    if "--package" in a:
        i = a.index("--package"); pkg = a[i + 1]; del a[i:i + 2]
    n, m = emit(a[0], a[1], ex, pkg)
    print(f"{n} requirements, {m} monitors -> {a[1]}")
