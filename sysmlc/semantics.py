"""IR -> z3 semantics: variables, KerML expressions (Boolean, enumerations, real arithmetic, if-then-else),
variant selectors, allocation variables and state-machine next-state relations."""
import re
from z3 import Int, Real, Bool, BoolVal, RealVal, IntVal, If, And, Or, Not, Implies, Xor

TOK = re.compile(r"\s*(<=|>=|==|!=|<|>|\?|\(|\)|\+|-|\*|/|\d+\.?\d*(?:[eE][-+]?\d+)?|[A-Za-z_][\w.]*(?:::\w+)?)")


def tokenize(s):
    """Strict lexer: every non-blank character must belong to a token; anything else is an error."""
    toks, i = [], 0
    while i < len(s):
        if s[i].isspace():
            i += 1; continue
        m = TOK.match(s, i)
        if not m or m.end() == i:
            raise SyntaxError(f"unexpected character {s[i]!r} at position {i} in {s!r}")
        toks.append(m.group(1)); i = m.end()
    return toks


class Expr:
    def __init__(self, resolve, enums):
        self.resolve, self.enums = resolve, enums

    def __call__(self, s):
        p = _P(self, tokenize(s))
        e = p.imp()
        if p.i != len(p.t):
            raise SyntaxError(f"trailing tokens in {s!r}: {p.t[p.i:]}")
        return e


class _P:
    def __init__(self, ctx, toks):
        self.c, self.t, self.i = ctx, toks, 0

    def pk(self): return self.t[self.i] if self.i < len(self.t) else None
    def nx(self): self.i += 1; return self.t[self.i - 1]

    def imp(self):
        if self.pk() == "if":
            self.nx(); c = self.imp(); self.expect("then", "?"); a = self.imp(); self.expect("else")
            return If(c, a, self.imp())
        a = self.or_()
        if self.pk() == "implies":
            self.nx(); return Implies(a, self.imp())
        return a

    def or_(self):
        a = self.xor()
        while self.pk() == "or": self.nx(); a = Or(a, self.xor())
        return a

    def xor(self):
        a = self.and_()
        while self.pk() == "xor": self.nx(); a = Xor(a, self.and_())
        return a

    def and_(self):
        a = self.not_()
        while self.pk() == "and": self.nx(); a = And(a, self.not_())
        return a

    def not_(self):
        if self.pk() == "not": self.nx(); return Not(self.not_())
        return self.cmp()

    def cmp(self):
        a = self.add()
        if self.pk() in ("<=", ">=", "==", "!=", "<", ">"):
            op = self.nx(); b = self.add()
            import operator as o
            return {"<=": o.le, ">=": o.ge, "==": o.eq, "!=": o.ne, "<": o.lt, ">": o.gt}[op](a, b)
        return a

    def add(self):
        a = self.mul()
        while self.pk() in ("+", "-"):
            op = self.nx(); b = self.mul(); a = a + b if op == "+" else a - b
        return a

    def mul(self):
        a = self.una()
        while self.pk() in ("*", "/"):
            op = self.nx(); b = self.una(); a = a * b if op == "*" else a / b
        return a

    def una(self):
        if self.pk() == "-": self.nx(); return -self.una()
        return self.atom()

    def expect(self, *ok):
        x = self.nx() if self.i < len(self.t) else None
        if x not in ok:
            raise SyntaxError(f"expected {' or '.join(ok)}, found {x!r}")
        return x

    def atom(self):
        if self.i >= len(self.t):
            raise SyntaxError("unexpected end of expression")
        x = self.nx()
        if x == "(":
            e = self.imp(); self.expect(")"); return e
        if re.match(r"\d", x):
            return RealVal(x)
        if x in ("true", "false"):
            return BoolVal(x == "true")
        if "::" in x:
            en, lit = x.split("::")
            if en not in self.c.enums or lit not in self.c.enums[en]:
                raise NameError(f"unknown enumeration literal {x}")
            return IntVal(self.c.enums[en].index(lit))
        if x in ("and", "or", "xor", "not", "implies", "then", "else", "if", ")", "?"):
            raise SyntaxError(f"unexpected {x!r}")
        return self.c.resolve(x)


class Semantics:
    def __init__(self, ir):
        self.ir = ir
        self.enums = ir["enums"]
        self.vars, self.vtype, dom = {}, {}, []
        self.errors = []
        for r in ir["requirements"].values():
            for a in r["attrs"]:
                n, ty = a["name"], a["type"]
                if n in self.vars:
                    if self.vtype[n] != ty:
                        self.errors.append(f"attribute '{n}' declared with types {self.vtype[n]} and {ty} "
                                           "(names are global signals; use distinct names)")
                    continue
                if ty == "Boolean":
                    self.vars[n] = Bool(n)
                elif ty in self.enums:
                    self.vars[n] = Int(n); dom.append(And(self.vars[n] >= 0, self.vars[n] < len(self.enums[ty])))
                else:
                    self.vars[n] = Real(n)
                self.vtype[n] = ty
        for a in ir["actions"].values():
            for n in a["inputs"]:
                self.vars.setdefault(n, Bool(n)); self.vtype.setdefault(n, "Boolean")
        sysd = ir["system"] or dict(usages={}, derived={})
        self.usages = {u: d for u, d in sysd["usages"].items() if d in ir["variations"]}
        self.sel = {u: Int(f"sel_{u}") for u in self.usages}
        dom += [And(s >= 0, s < len(ir["variations"][self.usages[u]])) for u, s in self.sel.items()]
        self.onboard = {}
        self.domain = And(*dom) if dom else BoolVal(True)
        self.undeclared = set()
        self.declared = {a["name"] for r in ir["requirements"].values() for a in r["attrs"]} | \
            {n for a in ir["actions"].values() for n in a["inputs"]}
        sysd0 = ir["system"] or dict(derived={})
        for n in sysd0.get("derived", {}):
            if n in self.vars:
                self.errors.append(f"derived attribute '{n}' has the same name as a requirement attribute")
        self.E = Expr(self.resolve, self.enums)
        self.R = {}
        for k, v in ir["requirements"].items():
            try:
                self.R[k] = self.E(v["expr"])
            except (SyntaxError, NameError, KeyError, ValueError) as ex:
                self.errors.append(f"requirement '{k}': {ex}")
        for m in ir["machines"].values():
            for t in m["transitions"]:
                try:
                    self.E(t["guard"])
                except (SyntaxError, NameError, KeyError, ValueError) as ex:
                    self.errors.append(f"transition '{t['id']}': {ex}")

    # name resolution: derived attribute > variant feature chain > allocation flag > signal (last chain segment)
    def resolve(self, name):
        sysd = self.ir["system"] or dict(derived={})
        parts = name.split(".")
        if parts[-1] in sysd["derived"] and (len(parts) == 1 or parts[0] not in self.usages):
            return Expr(self.resolve, self.enums)(sysd["derived"][parts[-1]])
        for i, seg in enumerate(parts[:-1]):          # skip a subject prefix such as 'sys.'
            if seg in self.usages:
                return self.variant_attr(seg, parts[i + 1])
        m = re.match(r"(\w+)OnBoard$", name)
        if m:
            return self.onboard.setdefault(m.group(1), Bool(f"onboard_{m.group(1)}"))
        if len(parts) > 1:                             # a feature chain must start at a subject, usage or port
            head = parts[0]
            if head in self.ir.get("ports", {}):
                pdef = self.ir["ports"][head][0]
                if len(parts) != 2 or parts[1] not in self.ir["port_defs"].get(pdef, []):
                    raise NameError(f"'{name}': port '{head}' ({pdef}) has no attribute '{parts[-1]}'")
            elif head not in self.ir.get("subjects", []) and head not in (self.ir["system"] or {}).get("usages", {}):
                raise NameError(f"'{name}': '{head}' is not a declared port, part usage or subject")
        last = name.split(".")[-1]
        if last in self.vars:
            return self.vars[last]
        mpre = re.match(r"pre\d+_(\w+)$", last)
        if not (mpre and (mpre.group(1) in self.vars or mpre.group(1) in self.declared)):
            # a name used in an expression but declared nowhere: almost always a typo. Kept as a free
            # Boolean so that analysis can continue, but reported as an error by the driver.
            self.undeclared.add(last)
        self.vars[last] = Bool(last); self.vtype[last] = "Boolean"
        return self.vars[last]

    def variant_attr(self, u, a):
        vs = self.ir["variations"][self.usages[u]]
        val = lambda x: BoolVal(x == "true") if x in ("true", "false") else RealVal(x)
        e = val(vs[-1][1][a])
        for k in range(len(vs) - 2, -1, -1):
            e = If(self.sel[u] == k, val(vs[k][1][a]), e)
        return e

    # state machines <-> requirement variables: the enum whose literals are the machine states
    def machine_vars(self, mname):
        m = self.ir["machines"][mname]
        enum = next(e for e, lits in self.enums.items() if set(lits) == set(m["states"]))
        attrs = [a for r in self.ir["requirements"].values() for a in r["attrs"] if a["type"] == enum]
        outs = {a["name"] for a in attrs if a["dir"] == "out"}
        cur = next(a["name"] for a in attrs if a["dir"] == "in" and a["name"] not in outs)
        nxt = next(iter(sorted(outs)))
        return enum, self.vars[cur], self.vars[nxt]

    def machine_relation(self, mname):
        """First enabled transition in textual order; none enabled -> stay (SysML semantics)."""
        m = self.ir["machines"][mname]
        enum, cur, nxt = self.machine_vars(mname)
        lits = self.enums[enum]
        cl = []
        for s in m["states"]:
            none = BoolVal(True)
            for t in [t for t in m["transitions"] if t["src"] == s]:
                g = self.E(t["guard"])
                cl.append(Implies(And(cur == lits.index(s), none, g), nxt == lits.index(t["dst"])))
                none = And(none, Not(g))
            cl.append(Implies(And(cur == lits.index(s), none), nxt == lits.index(s)))
        return And(*cl)


class CompileError(Exception):
    """Raised when the model cannot be translated faithfully; no analysis result is produced."""

    def __init__(self, path, errors):
        self.path, self.errors = path, errors
        super().__init__(f"{path}: {len(errors)} error(s)\n" + "\n".join(f"  ERROR: {e}" for e in errors))


def compile_model(path):
    """Parse and translate a model, failing closed: any parse error, unsupported construct, type clash,
    malformed expression or undeclared name raises CompileError."""
    from parser import parse
    ir = parse(path)
    if ir["errors"]:
        raise CompileError(path, ir["errors"])
    S = Semantics(ir)
    for name, expr in ir["asserts"].items():            # port contracts are used later; parse them now, strictly
        try:
            S.E(expr)
        except Exception as ex:
            S.errors.append(f"assert constraint '{name}': {ex}")
    for aname, a in ir["actions"].items():               # decision guards of action flows
        for _, _, g in a["edges"]:
            if g:
                try:
                    S.E(g)
                except Exception as ex:
                    S.errors.append(f"action '{aname}': guard '{g}': {ex}")
    errs = list(S.errors) + [f"name '{n}' is used but not declared" for n in sorted(S.undeclared)]
    if errs:
        raise CompileError(path, errs)
    return S
