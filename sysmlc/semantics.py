"""IR -> z3 semantics: variables, KerML expressions (Boolean, enumerations, real arithmetic, if-then-else),
variant selectors, allocation variables and state-machine next-state relations."""
import os, re
from z3 import Int, Real, Bool, BoolVal, RealVal, IntVal, If, And, Or, Not, Implies, Xor, ToReal, is_int, is_bool

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
    def __init__(self, resolve, enums, is_enum=lambda name: None):
        self.resolve, self.enums, self.is_enum = resolve, enums, is_enum

    def __call__(self, s):
        p = _P(self, tokenize(s))
        e = p.imp()
        if p.i != len(p.t):
            raise SyntaxError(f"trailing tokens in {s!r}: {p.t[p.i:]}")
        return e


class _P:
    def __init__(self, ctx, toks):
        self.c, self.t, self.i = ctx, toks, 0
        self.enum_terms = []

    def pk(self): return self.t[self.i] if self.i < len(self.t) else None
    def nx(self): self.i += 1; return self.t[self.i - 1]

    def imp(self):
        if self.pk() == "if":
            self.nx(); c = self.imp(); self.expect("then", "?"); a = self.imp(); self.expect("else")
            b = self.imp()
            self._bool(c)
            if is_bool(a) != is_bool(b):
                raise TypeError("branches of a conditional mix a Boolean and a number")
            ea, eb = self._etype(a), self._etype(b)
            if ea != eb and (ea or eb):
                raise TypeError(f"branches of a conditional have different types ({ea or 'number'} and {eb or 'number'})")
            r = If(c, a, b)
            if ea:
                self.enum_terms.append((r, ea))
            return r
        a = self.or_()
        if self.pk() == "implies":
            self.nx(); b = self.imp(); self._bool(a, b); return Implies(a, b)
        return a

    def or_(self):
        a = self.xor()
        while self.pk() == "or": self.nx(); b = self.xor(); self._bool(a, b); a = Or(a, b)
        return a

    def xor(self):
        a = self.and_()
        while self.pk() == "xor": self.nx(); b = self.and_(); self._bool(a, b); a = Xor(a, b)
        return a

    def and_(self):
        a = self.not_()
        while self.pk() == "and": self.nx(); b = self.not_(); self._bool(a, b); a = And(a, b)
        return a

    def not_(self):
        if self.pk() == "not": self.nx(); a = self.not_(); self._bool(a); return Not(a)
        return self.cmp()

    @staticmethod
    def _bool(*ts):
        """Operands of and, or, xor, not, implies and conditions must be Boolean (no coercion from numbers)."""
        for t in ts:
            if not is_bool(t):
                raise TypeError(f"'{t}' is a number where a Boolean is required")

    @staticmethod
    def _num(*ts):
        """Operands of arithmetic and order comparisons must be numbers (no coercion of Booleans to 0/1)."""
        for t in ts:
            if is_bool(t):
                raise TypeError(f"Boolean '{t}' used in arithmetic or in an order comparison")

    def _etype(self, t):
        """Enumeration type of a term, or None."""
        for e, en in self.enum_terms:
            if t is e:                  # the same parsed term, not a structurally equal one (indices coincide)
                return en
        return None

    def _enum(self, *ts):
        """Enumeration values admit only == and != between values of the same enumeration (KerML enumerations are
        unordered); order comparisons, arithmetic and comparisons with numbers or other enumerations are rejected,
        so that the translation to integer indices preserves the meaning."""
        for t in ts:
            if self._etype(t):
                raise TypeError(f"enumeration value {t} used with an order comparison or arithmetic")

    def cmp(self):
        a = self.add()
        if self.pk() in ("<=", ">=", "==", "!=", "<", ">"):
            op = self.nx(); b = self.add()
            if op not in ("==", "!="):
                self._num(a, b)
                self._enum(a, b)
            else:
                if is_bool(a) != is_bool(b):
                    raise TypeError(f"comparison of a Boolean with a number ('{a}' {op} '{b}')")
                ea, eb = self._etype(a), self._etype(b)
                if ea != eb and (ea or eb):
                    raise TypeError(f"comparison of {ea or 'a number'} with {eb or 'a number'}")
            import operator as o
            return {"<=": o.le, ">=": o.ge, "==": o.eq, "!=": o.ne, "<": o.lt, ">": o.gt}[op](a, b)
        return a

    def add(self):
        a = self.mul()
        while self.pk() in ("+", "-"):
            op = self.nx(); b = self.mul(); self._num(a, b); self._enum(a, b); a = a + b if op == "+" else a - b
        return a

    def mul(self):
        a = self.una()
        while self.pk() in ("*", "/"):
            op = self.nx(); b = self.una(); self._num(a, b); self._enum(a, b)
            if op == "/" and is_int(a) and is_int(b):       # KerML: Integer / Integer is a Rational, not truncated
                a = ToReal(a)
            a = a * b if op == "*" else a / b
        return a

    def una(self):
        if self.pk() == "-":
            self.nx(); a = self.una(); self._num(a); self._enum(a); return -a
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
            v = IntVal(self.c.enums[en].index(lit)); self.enum_terms.append((v, en))
            return v
        if x in ("and", "or", "xor", "not", "implies", "then", "else", "if", ")", "?"):
            raise SyntaxError(f"unexpected {x!r}")
        v = self.c.resolve(x)
        en = self.c.is_enum(x)
        if en:
            self.enum_terms.append((v, en))
        return v


BASIC_TYPES = ("Boolean", "Integer", "Real")


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
                if ty not in BASIC_TYPES and ty not in self.enums:
                    self.errors.append(f"attribute '{n}' has type '{ty}', which is neither Boolean, Integer, Real "
                                       "nor a declared enumeration")
                    continue
                if ty == "Boolean":
                    self.vars[n] = Bool(n)
                elif ty in self.enums:
                    self.vars[n] = Int(n); dom.append(And(self.vars[n] >= 0, self.vars[n] < len(self.enums[ty])))
                elif ty == "Integer":
                    self.vars[n] = Int(n)
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
        self.E = Expr(self.resolve, self.enums, self._enum_of)
        for n, ty in ir.get("part_attrs", {}).items():
            if ty not in BASIC_TYPES and ty not in self.enums and ty not in ir.get("port_defs", {}) \
                    and ty not in ir.get("variations", {}):
                self.errors.append(f"part attribute '{n}' has type '{ty}', which is neither Boolean, Integer, Real "
                                   "nor a declared enumeration")
        self.R = {}
        for k, v in ir["requirements"].items():
            try:
                self.R[k] = self.boolean(v["expr"], "require constraint")
            except (SyntaxError, NameError, KeyError, ValueError, TypeError) as ex:
                self.errors.append(f"requirement '{k}': {ex}")
        for m in ir["machines"].values():
            for t in m["transitions"]:
                try:
                    self.boolean(t["guard"], "guard")
                except (SyntaxError, NameError, KeyError, ValueError, TypeError) as ex:
                    self.errors.append(f"transition '{t['id']}': {ex}")

    def boolean(self, text, what):
        """Translate an expression that must denote a Boolean (constraint, guard, assertion)."""
        e = self.E(text)
        if not is_bool(e):
            raise TypeError(f"the {what} '{text}' is not a Boolean expression")
        return e

    def _enum_of(self, name):
        ty = self.vtype.get(name.split(".")[-1])
        return ty if ty in self.enums else None

    # name resolution: derived attribute > variant feature chain > allocation flag > signal (last chain segment)
    def resolve(self, name):
        sysd = self.ir["system"] or dict(derived={})
        parts = name.split(".")
        if parts[-1] in sysd["derived"] and (len(parts) == 1 or parts[0] not in self.usages):
            return Expr(self.resolve, self.enums, self._enum_of)(sysd["derived"][parts[-1]])
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
        pty = self.ir.get("part_attrs", {}).get(last)
        if pty and len(parts) > 1:                     # an attribute of a part definition, reached by a chain
            self.vars[last] = Bool(last) if pty == "Boolean" else Int(last) if pty == "Integer" else Real(last)
            self.vtype[last] = pty
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
        """The enumeration whose literals are the machine's states, and the unique pair (current, next) of attributes
        of that type: the current state is the only attribute of the type read as input and never written, the next
        state the only one written as output. Any other situation (no such enumeration, two enumerations with the
        same literals, two machines over one enumeration, or more than one candidate attribute) is ambiguous and
        rejected; the binding is never guessed."""
        m = self.ir["machines"][mname]
        enums = [e for e, lits in self.enums.items() if set(lits) == set(m["states"])]
        if len(enums) != 1:
            raise TypeError(f"machine '{mname}': {'no' if not enums else 'more than one'} enumeration has exactly its "
                            f"states as literals")
        enum = enums[0]
        others = [n for n, x in self.ir["machines"].items() if n != mname and set(x["states"]) == set(m["states"])]
        if others:
            raise TypeError(f"machines '{mname}' and '{others[0]}' have the same states, so their current/next "
                            f"attributes of type {enum} cannot be bound unambiguously")
        attrs = [a for r in self.ir["requirements"].values() for a in r["attrs"] if a["type"] == enum]
        outs = sorted({a["name"] for a in attrs if a["dir"] == "out"})
        ins = sorted({a["name"] for a in attrs if a["dir"] == "in" and a["name"] not in outs})
        if len(ins) != 1 or len(outs) != 1:
            raise TypeError(f"machine '{mname}': expected one current-state attribute (in) and one next-state "
                            f"attribute (out) of type {enum}, found in={ins} out={outs}")
        return enum, self.vars[ins[0]], self.vars[outs[0]]

    def machine_relation(self, mname, semantics=None):
        """Step relation of a state machine. 'priority' (default): the first enabled transition in textual order
        fires; 'nondet': any enabled transition may fire. In both, a state with no enabled transition persists
        (SysML). Select with the environment variable SYSMLC_MACHINE_SEMANTICS or the argument."""
        semantics = semantics or os.environ.get("SYSMLC_MACHINE_SEMANTICS", "priority")
        m = self.ir["machines"][mname]
        enum, cur, nxt = self.machine_vars(mname)
        lits = self.enums[enum]
        if semantics == "nondet":
            cl = []
            for s in m["states"]:
                ts = [t for t in m["transitions"] if t["src"] == s]
                gs = [self.E(t["guard"]) for t in ts]
                here = cur == lits.index(s)
                if ts:
                    cl.append(Implies(And(here, Or(*gs)), Or(*[And(g, nxt == lits.index(t["dst"])) for g, t in zip(gs, ts)])))
                cl.append(Implies(And(here, Not(Or(*gs)) if gs else BoolVal(True)), nxt == lits.index(s)))
            return And(*cl)
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
            S.boolean(expr, "assert constraint")
        except Exception as ex:
            S.errors.append(f"assert constraint '{name}': {ex}")
    for aname, a in ir["actions"].items():               # decision guards of action flows
        for _, _, g in a["edges"]:
            if g:
                try:
                    S.boolean(g, "decision guard")
                except Exception as ex:
                    S.errors.append(f"action '{aname}': guard '{g}': {ex}")
    for mname in ir["machines"]:                          # unambiguous binding of every machine to its signals
        try:
            S.machine_vars(mname)
        except TypeError as ex:
            S.errors.append(str(ex))
    errs = list(S.errors) + [f"name '{n}' is used but not declared" for n in sorted(S.undeclared)]
    if errs:
        raise CompileError(path, errs)
    return S
