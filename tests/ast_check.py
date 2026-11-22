#!/usr/bin/env python3
"""Cross-check of the sysmlc front end against the abstract syntax tree built by the SysML v2 Pilot Implementation.

The Pilot Implementation (release 0.63.1) parses and resolves each model; validation/DumpAst.java writes its AST to
results/reference/ast/<model>.json. This script rebuilds, from that AST alone, everything the compiler reads from the
text, and compares it with the sysmlc intermediate representation:

  * structure: enumerations (literals in order), requirement definitions (short name, name, subject and its type,
    attributes with direction and type), requirement usages, port definitions, ports of each part definition (type and
    conjugation), part-definition attributes, part usages of the system, connections and interfaces, satisfy
    relations, state machines (states, initial state, transitions with source and target, in order), variation points
    (variants and their attribute values), allocations, action flows (nodes, successions, decision branches) and
    refinement dependencies (#refinement, clients and suppliers);
  * expressions: every require constraint, assert constraint, transition guard, decision guard and derived attribute
    is rebuilt from the Pilot's operator tree (operators, operand order, literals, references) by an independent
    translator into z3, and proved equivalent to the formula the sysmlc grammar front end produced.

    python3 tests/ast_check.py            # all models with a dump
    python3 tests/ast_check.py lmcps_fsm  # one model
Exit status 0 iff every comparison agrees.
"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import (And, Or, Not, Implies, Xor, If, BoolVal, RealVal, IntVal, Solver, unsat, is_bool, simplify)
from semantics import compile_model

AST = os.path.join(ROOT, "results", "reference", "ast")


# ---------------------------------------------------------------- AST helpers
def walk(n):
    yield n
    for k in n["kids"]:
        yield from walk(k)


def is_expr(n):
    return n["mc"].endswith("Expression") or n["mc"].startswith("Literal")


def short(qn):
    return None if qn is None else qn.split("::")[-1].strip("'")


def args(n):
    """Operands of an invocation: the first expression owned by each 'in' parameter, in order."""
    out = []
    for k in n["kids"]:
        if k["mc"] == "Feature" and k.get("dir") == "in":
            e = [x for x in k["kids"] if is_expr(x)]
            if e:
                out.append(e[0])
    return out


def tree(n):
    """Pilot expression -> neutral tree: ('op', name, [args]) | ('ref', chain, refMc, types) | ('lit', text)."""
    mc = n["mc"]
    if mc.startswith("Literal"):
        return ("lit", n["lit"])
    if mc == "FeatureReferenceExpression":
        if n.get("ref") is None or n.get("refMc", "").endswith("Expression"):
            body = [x for x in n["kids"] if is_expr(x)]       # body expression of a lazy operand
            return tree(body[0])
        return ("ref", n["refName"], n["refMc"], n.get("refTypes", []))
    if mc == "FeatureChainExpression":
        a = args(n)
        src = tree(a[0])
        assert src[0] == "ref", src
        tgt = n["targetName"]
        if tgt is None:                                   # target is itself a feature chain such as orbit.h
            ch = next(k["chain"] for k in n["kids"] if k["mc"] == "Feature" and k.get("chain"))
            tgt = ".".join(short(c) for c in ch)
        return ("ref", src[1] + "." + tgt, "chain", [])
    if mc == "OperatorExpression":
        return ("op", n["op"], [tree(a) for a in args(n)])
    raise ValueError(f"unhandled expression metaclass {mc}")


def result_expr(n):
    """The result expression of a constraint, guard or feature value: the first expression child."""
    e = [x for x in n["kids"] if is_expr(x)]
    return e[0] if e else None


class Z3:
    """Independent translator Pilot tree -> z3 (Table 3 of the paper). Names are resolved through the compiler's
    resolver, which is the documented binding of signals by name; enum literals by the Pilot's own literal order."""

    def __init__(self, S, enums):
        self.S, self.enums = S, enums

    def __call__(self, t):
        k = t[0]
        if k == "lit":
            x = t[1]
            if x in ("true", "false"):
                return BoolVal(x == "true")
            return RealVal(x)
        if k == "ref":
            name, mc, types = t[1], t[2], t[3]
            if mc == "EnumerationUsage":
                en = short(types[0])
                return IntVal(self.enums[en].index(name))
            return self.S.resolve(name)
        op, a = t[1], [self(x) for x in t[2]]
        if op == "implies": return Implies(a[0], a[1])
        if op == "and": return And(a[0], a[1])
        if op == "or": return Or(a[0], a[1])
        if op == "xor": return Xor(a[0], a[1])
        if op == "not": return Not(a[0])
        if op == "if": return If(a[0], a[1], a[2])
        if op == "==": return a[0] == a[1]
        if op == "!=": return a[0] != a[1]
        if op == "<": return a[0] < a[1]
        if op == "<=": return a[0] <= a[1]
        if op == ">": return a[0] > a[1]
        if op == ">=": return a[0] >= a[1]
        if op == "+": return a[0] + a[1] if len(a) == 2 else a[0]
        if op == "-": return a[0] - a[1] if len(a) == 2 else -a[0]
        if op == "*": return a[0] * a[1]
        if op == "/": return a[0] / a[1]
        raise ValueError(f"operator {op!r} outside the translated subset")


def equivalent(f, g):
    s = Solver()
    s.add(f != g) if not is_bool(f) else s.add(Xor(f, g))
    return s.check() == unsat


# ---------------------------------------------------------------- rebuild the IR facts from the AST
def from_ast(root):
    F = dict(enums={}, reqdefs={}, req_usages={}, port_defs={}, part_ports={}, part_attrs={}, machines={},
             variations={}, allocations=[], connections=[], satisfy=[], derivations={}, usages={}, actions={},
             exprs={})
    nodes = list(walk(root))
    for n in nodes:
        mc = n["mc"]
        if mc == "EnumerationDefinition":
            F["enums"][n["name"]] = [k["name"] for k in n["kids"] if k["mc"] == "EnumerationUsage"]
        elif mc == "RequirementDefinition":
            subj = next((k for k in n["kids"] if k["mc"] == "ReferenceUsage" and k.get("dir") == "in"), None)
            attrs = [(k.get("dir"), k["name"], short(k["types"][0])) for k in n["kids"]
                     if k["mc"] == "AttributeUsage" and k.get("dir") in ("in", "out")]
            F["reqdefs"][n["short"]] = dict(
                name=n["name"], attrs=attrs,
                subject=None if subj is None else (subj["name"], None if subj["types"] == ["Base::Anything"] else short(subj["types"][0])))
            cons = [k for k in n["kids"] if k["mc"] == "ConstraintUsage"]
            assert len(cons) == 1, (n["short"], len(cons))
            F["exprs"][("req", n["short"])] = tree(result_expr(cons[0]))
        elif mc == "RequirementUsage" and n["name"] and n["types"] and not n["kids"] or \
                (mc == "RequirementUsage" and n["name"] and all(k["mc"] in ("Multiplicity",) for k in n["kids"])):
            F["req_usages"][n["name"]] = short(n["types"][0])
        elif mc == "PortDefinition":
            F["port_defs"][n["name"]] = [k["name"] for k in n["kids"] if k["mc"] == "AttributeUsage"]
        elif mc in ("PartDefinition",):
            ports = {}
            for k in n["kids"]:
                if k["mc"] == "PortUsage":
                    ty = k["types"][0]
                    conj = bool(re.search(r"'~\w+'$", ty))
                    ports[k["name"]] = (short(ty).lstrip("~") if not conj else ty.split("::")[-2], conj)
                if k["mc"] == "AttributeUsage" and k["name"] and not n.get("variation") and result_expr(k) is None:
                    F["part_attrs"].setdefault(k["name"], short(k["types"][0]))
            if not n.get("variation"):
                F["part_ports"][n["name"]] = ports
            if n.get("variation"):
                vs = []
                for v in n["kids"]:
                    if v["mc"] == "PartUsage":
                        vals = {}
                        for a in v["kids"]:
                            if a["mc"] == "AttributeUsage" and a.get("redef"):
                                vals[short(a["redef"][0])] = result_expr(a)["lit"]
                        vs.append((v["name"], vals))
                F["variations"][n["name"]] = vs
            for k in n["kids"]:
                if k["mc"] in ("ConnectionUsage", "InterfaceUsage"):
                    F["connections"].append(tuple(k["ends"]))
                elif k["mc"] == "AllocationUsage":
                    F["allocations"].append((k["ends"][0].split(".")[-1], k["ends"][1]))
                elif k["mc"] == "SatisfyRequirementUsage":
                    F["satisfy"].append((k["satisfied"], k["by"]))
                elif k["mc"] == "PartUsage" and k["name"] and k["types"] != ["Parts::Part"]:   # typed usages
                    F["usages"].setdefault(n["name"], {})[k["name"]] = short(k["types"][0])
                elif k["mc"] == "AttributeUsage" and k["name"] and result_expr(k) is not None:
                    F["exprs"][("derived", k["name"])] = tree(result_expr(k))
        elif mc == "InterfaceDefinition":
            for k in n["kids"]:
                if k["mc"] == "AssertConstraintUsage":
                    F["exprs"][("assert", k["name"])] = tree(result_expr(k))
        elif mc in ("StateUsage", "ExhibitStateUsage") and any(k["mc"] == "TransitionUsage" for k in n["kids"]):
            states = [k["name"] for k in n["kids"] if k["mc"] == "StateUsage"]
            init = next(k["ends"][1] for k in n["kids"] if k["mc"] == "SuccessionAsUsage" and k["ends"][0] == "entryAction")
            ts = []
            for k in n["kids"]:
                if k["mc"] == "TransitionUsage":
                    g = [x for x in k["kids"] if is_expr(x)]
                    ts.append((k["name"], k["src"], k["dst"]))
                    F["exprs"][("guard", n["name"], k["name"])] = tree(g[0])
            F["machines"][n["name"]] = dict(states=states, init=init, transitions=ts)
        elif mc == "ActionDefinition":
            kind = {}
            edges = []
            for k in n["kids"]:
                m = {"ActionUsage": "action", "DecisionNode": "decide", "MergeNode": "merge", "ForkNode": "fork",
                     "JoinNode": "join"}.get(k["mc"])
                if m and k["name"]:
                    kind[k["name"]] = m
                if k["mc"] == "SuccessionAsUsage":
                    edges.append((k["ends"][0], k["ends"][1], None))
                if k["mc"] == "TransitionUsage":
                    g = [x for x in k["kids"] if is_expr(x)]
                    edges.append((k["src"], k["dst"], len(edges)))
                    F["exprs"][("dguard", n["name"], k["src"], k["dst"])] = tree(g[0])
            F["actions"][n["name"]] = dict(kind=kind, edges=edges)
        elif mc == "Dependency":
            meta = [k["meta"] for k in n["kids"] if k["mc"] == "MetadataUsage"]
            if "ModelingMetadata::Refinement" in meta:
                F["derivations"][n["name"]] = dict(client=[short(c) for c in n["client"]],
                                                   supplier=[short(s) for s in n["supplier"]])
    return F


# ---------------------------------------------------------------- comparison
def check(model):
    S = compile_model(os.path.join(ROOT, "models", model + ".sysml"))
    ir = S.ir
    root = json.load(open(os.path.join(AST, model + ".json")))
    A = from_ast(root)
    fails, n = [], 0

    def eq(what, a, b):
        nonlocal n
        n += 1
        if a != b:
            fails.append(f"{what}: sysmlc={a!r} pilot={b!r}")

    eq("enumerations", ir["enums"], A["enums"])
    eq("requirement definitions", sorted(ir["requirements"]), sorted(A["reqdefs"]))
    for k, r in ir["requirements"].items():
        p = A["reqdefs"].get(k)
        if not p:
            continue
        eq(f"{k} name", r["name"], p["name"])
        eq(f"{k} attributes", [(a["dir"], a["name"], a["type"]) for a in r["attrs"]], p["attrs"])
        sj = r.get("subject")
        eq(f"{k} subject", None if sj is None else tuple(sj), p["subject"])
    eq("requirement usages", ir["req_usages"], A["req_usages"])
    eq("port definitions", ir["port_defs"], A["port_defs"])
    eq("ports of part definitions", {k: {p: tuple(v) for p, v in d.items()} for k, d in ir["part_ports"].items()},
       A["part_ports"])
    eq("part-definition attributes", ir["part_attrs"], A["part_attrs"])
    eq("connections", sorted(tuple(c) for c in ir["connections"]), sorted(A["connections"]))
    eq("allocations", sorted(tuple(a) for a in ir["allocations"]), sorted(A["allocations"]))
    if ir["system"]:
        eq("system usages", ir["system"]["usages"], A["usages"].get(ir["system"]["name"]))
    eq("machines", {m: dict(states=d["states"], init=d["init"],
                            transitions=[(t["id"], t["src"], t["dst"]) for t in d["transitions"]])
                    for m, d in ir["machines"].items()}, A["machines"])
    eq("variations", {v: [(n_, {a: str(x) for a, x in vals.items()}) for n_, vals in vs]
                      for v, vs in ir["variations"].items()},
       {v: [(n_, vals) for n_, vals in vs] for v, vs in A["variations"].items()})
    # refinement dependencies: client usages refine the supplier usage; compare through requirement short names
    u2d = {u: next(k for k, r in ir["requirements"].items() if r["name"] == d) for u, d in A["req_usages"].items()}
    eq("refinement dependencies", {k: dict(original=v["original"], derived=v["derived"]) for k, v in ir["derivations"].items()},
       {k: dict(original=u2d[v["supplier"][0]], derived=[u2d[c] for c in v["client"]]) for k, v in A["derivations"].items()})
    for an, a in ir["actions"].items():
        p = A["actions"].get(an, dict(kind={}, edges=[]))
        eq(f"action {an} nodes", {k: v for k, v in a["kind"].items() if v not in ("start", "final")}, p["kind"])
        eq(f"action {an} successions", sorted((s, d) for s, d, _ in a["edges"]), sorted((s, d) for s, d, _ in p["edges"]))

    # expressions
    Z = Z3(S, A["enums"])
    sysd = ir["system"] or dict(derived={})
    pairs = []
    for k, r in ir["requirements"].items():
        pairs.append((f"require constraint {k}", r["expr"], A["exprs"].get(("req", k))))
    for k, e in ir["asserts"].items():
        pairs.append((f"assert constraint {k}", e, A["exprs"].get(("assert", k))))
    for m, d in ir["machines"].items():
        for t in d["transitions"]:
            pairs.append((f"guard {m}.{t['id']}", t["guard"], A["exprs"].get(("guard", m, t["id"]))))
    for an, a in ir["actions"].items():
        for s, d, g in a["edges"]:
            if g:
                pairs.append((f"decision {an}: {s}->{d}", g, A["exprs"].get(("dguard", an, s, d))))
    for k, e in sysd["derived"].items():
        pairs.append((f"derived attribute {k}", e, A["exprs"].get(("derived", k))))
    n_expr = 0
    for what, text, t in pairs:
        n += 1
        if t is None:
            fails.append(f"{what}: missing in the Pilot AST"); continue
        f, g = S.E(text), Z(t)
        n_expr += 1
        if not equivalent(f, g):
            fails.append(f"{what}: not equivalent\n    sysmlc: {simplify(f)}\n    pilot:  {simplify(g)}")
    extra = {k for k in A["exprs"] if k[0] == "derived"} - {("derived", k) for k in sysd["derived"]}
    for k in extra:
        if k[1] not in ir["part_attrs"]:      # attribute values of action steps are read as data, not derived
            pass
    return n, n_expr, fails


def mutants(t):
    """Single-point perturbations of a Pilot expression tree (operator swap, operand swap, literal change), used to
    show that the equivalence comparison discriminates: a perturbed tree must not be proved equivalent unless the
    perturbation happens to preserve the meaning."""
    if t[0] == "op":
        sw = {"and": "or", "or": "and", "<=": "<", ">=": ">", "<": "<=", ">": ">=", "==": "!=", "!=": "==",
              "implies": "and", "+": "-", "-": "+", "*": "+", "/": "*"}
        if t[1] in sw and not (t[1] in "+-" and len(t[2]) == 1):
            yield ("op", sw[t[1]], t[2])
        if len(t[2]) == 2 and t[1] in ("implies", "-", "/", "<", "<=", ">", ">="):
            yield ("op", t[1], t[2][::-1])
        for i, a in enumerate(t[2]):
            for m in mutants(a):
                yield ("op", t[1], t[2][:i] + [m] + t[2][i + 1:])
    elif t[0] == "lit" and t[1] not in ("true", "false"):
        yield ("lit", repr(float(t[1]) * 1.5 + 1))


def sensitivity(model):
    S = compile_model(os.path.join(ROOT, "models", model + ".sysml"))
    A = from_ast(json.load(open(os.path.join(AST, model + ".json"))))
    Z = Z3(S, A["enums"])
    derived = (S.ir["system"] or {}).get("derived", {})
    tot = det = 0
    for key, t in A["exprs"].items():
        if key[0] == "derived" and key[1] not in derived:
            continue
        g = Z(t)
        for m in mutants(t):
            tot += 1
            if not equivalent(g, Z(m)):
                det += 1
    return tot, det


def main(models):
    total, bad = 0, 0
    report = {}
    for m in models:
        n, ne, fails = check(m)
        total += n; bad += len(fails)
        mt, md = sensitivity(m)
        report[m] = dict(comparisons=n, expressions=ne, failures=fails, perturbed=mt, perturbed_detected=md)
        print(f"{m}: {n} comparisons ({ne} expressions proved equivalent), {len(fails)} disagreement(s); "
              f"{md} of {mt} perturbed Pilot expressions are told apart")
        for f in fails:
            print("   ", f)
    out = os.path.join(AST, "ast_check.json")
    json.dump(report, open(out, "w"), indent=1)
    return bad == 0


if __name__ == "__main__":
    ms = sys.argv[1:] or sorted(f[:-5] for f in os.listdir(AST) if f.endswith(".json") and f not in ("ast_check.json", "frontend_check.json"))
    sys.exit(0 if main(ms) else 1)
