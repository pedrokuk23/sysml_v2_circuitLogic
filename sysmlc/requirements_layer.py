#!/usr/bin/env python3
"""Circuit reading of the requirement layer of ANY SysML v2 model the Pilot Implementation parses.

The compiler proper translates a subset and rejects everything else. A third-party model usually lies outside that
subset (units, items, timeslices, calculations, ...), but its requirement layer can still be read as a circuit:

  * every 'require constraint' is a gate; its inputs are the features its expression references (lines);
  * a line is TIED when its declaration gives it a value, DRIVEN when something outside the requirement that declares
    it gives it a value or refers to it (a redefinition, a binding, a reference from another element), and UNDRIVEN
    otherwise;
  * two gates CONTEND only through a shared line; gates without shared lines cannot conflict;
  * a gate is translated with the Table 3 operators; quantity literals 'v [unit]' are read as the magnitude v in the
    unit written (units are compared by name; a gate mixing different units for one dimension is flagged);
  * each gate is classified: always true, always false (under its tied lines), or open (its value depends on
    undriven or driven lines);
  * every #refinement dependency is classified as checkable (both ends requirements with gates and at least one shared
    line) or not, with the reason;
  * every satisfy relation is classified by whether it binds any input of the requirement it satisfies.

    python3 sysmlc/requirements_layer.py AST.json [OUT.json]      (AST from validation/DumpAst.java)
"""
import collections, json, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import Real, Int, Bool, And, Or, Not, Implies, Xor, If, BoolVal, RealVal, Solver, sat, unsat, is_bool

OPS = {"implies", "and", "or", "xor", "not", "if", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/", "["}


def walk(n, parent=None):
    yield n, parent
    for k in n["kids"]:
        yield from walk(k, n)


def is_expr(n):
    return n["mc"].endswith("Expression") or n["mc"].startswith("Literal")


def result_expr(n):
    e = [x for x in n["kids"] if is_expr(x)]
    return e[0] if e else None


def args(n):
    out = []
    for k in n["kids"]:
        if k["mc"] == "Feature" and k.get("dir") == "in":
            e = [x for x in k["kids"] if is_expr(x)]
            if e:
                out.append(e[0])
    return out


class Untranslated(Exception):
    pass


def is_unit(n):
    return any(t.split("::")[-1].endswith("Unit") or t.split("::")[-1] == "DimensionOneUnit"
               for t in n.get("refTypes", []))


def unit_text(n):
    """Readable unit of a unit expression (metre / second -> 'metre/second')."""
    if n["mc"] == "FeatureReferenceExpression":
        return n.get("refName") or "?"
    if n["mc"] == "OperatorExpression":
        a = args(n)
        return f"({'/'.join(unit_text(x) for x in a)})" if n["op"] == "/" else \
               f"({'*'.join(unit_text(x) for x in a)})" if n["op"] == "*" else f"{n['op']}?"
    return "?"


class Gate:
    def __init__(self, req, node):
        self.req, self.node = req, node
        self.refs = []           # (qn, name, types, refMc)
        self.units = set()
        self.ops = collections.Counter()

    def scan(self, n):
        mc = n["mc"]
        if mc == "FeatureReferenceExpression":
            if n.get("ref") is None or n.get("refMc", "").endswith("Expression"):
                for x in n["kids"]:
                    if is_expr(x):
                        self.scan(x)
                return
            if is_unit(n):
                return
            self.refs.append((n["ref"], n["refName"], tuple(n.get("refTypes", [])), n["refMc"]))
            return
        if mc == "FeatureChainExpression":
            src = args(n)[0]
            self.scan(src)
            return
        if mc == "OperatorExpression":
            self.ops[n["op"]] += 1
            if n["op"] == "[":
                a = args(n)
                self.units.add(unit_text(a[1]))
                self.scan(a[0])
                return
            for a in args(n):
                self.scan(a)
            return
        for k in n["kids"]:
            if is_expr(k) or k["mc"] == "Feature":
                self.scan(k)


def z3_of(n, var):
    """Pilot expression -> z3 (Table 3 operators; 'v [unit]' read as v)."""
    mc = n["mc"]
    if mc.startswith("LiteralBoolean"):
        return BoolVal(n["lit"] == "true")
    if mc in ("LiteralInteger", "LiteralRational"):
        return RealVal(n["lit"])
    if mc == "FeatureReferenceExpression":
        if n.get("ref") is None or n.get("refMc", "").endswith("Expression"):
            return z3_of([x for x in n["kids"] if is_expr(x)][0], var)
        return var(n["ref"], n.get("refTypes", []))
    if mc == "FeatureChainExpression":
        raise Untranslated("feature chain")
    if mc == "OperatorExpression":
        op = n["op"]
        if op not in OPS:
            raise Untranslated(f"operator {op}")
        a = args(n)
        if op == "[":
            return z3_of(a[0], var)
        v = [z3_of(x, var) for x in a]
        f = {"implies": lambda: Implies(v[0], v[1]), "and": lambda: And(v[0], v[1]), "or": lambda: Or(v[0], v[1]),
             "xor": lambda: Xor(v[0], v[1]), "not": lambda: Not(v[0]), "if": lambda: If(v[0], v[1], v[2]),
             "==": lambda: v[0] == v[1], "!=": lambda: v[0] != v[1], "<": lambda: v[0] < v[1],
             "<=": lambda: v[0] <= v[1], ">": lambda: v[0] > v[1], ">=": lambda: v[0] >= v[1],
             "+": lambda: v[0] + v[1] if len(v) == 2 else v[0], "-": lambda: v[0] - v[1] if len(v) == 2 else -v[0],
             "*": lambda: v[0] * v[1], "/": lambda: v[0] / v[1]}[op]
        return f()
    raise Untranslated(mc)


def analyse(root):
    nodes = list(walk(root))
    by_qn = {}
    parent_of = {}
    for n, p in nodes:
        parent_of[id(n)] = p
        if n.get("qn") and n["mc"] in ("AttributeUsage", "ReferenceUsage", "Feature", "PartUsage", "ItemUsage"):
            by_qn.setdefault(n["qn"], n)
    reqs = [n for n, _ in nodes if n["mc"] in ("RequirementDefinition", "RequirementUsage")]
    gates = []
    for r in reqs:
        for c in r["kids"]:
            if c["mc"] == "ConstraintUsage" and (c.get("dir") is None):
                e = result_expr(c)
                if e is None:
                    continue
                g = Gate(r, e)
                g.scan(e)
                gates.append(g)

    # every reference to a feature, with the requirement subtree it occurs in (None if outside requirements)
    def subtree_ids(n):
        return {id(x) for x, _ in walk(n)}
    req_ids = {id(r): subtree_ids(r) for r in reqs}
    owner_req = {}
    for r in reqs:
        for i in req_ids[id(r)]:
            owner_req.setdefault(i, r["qn"])
    refs_outside = collections.Counter()
    redefined = collections.Counter()
    for n, _ in nodes:
        if n["mc"] == "FeatureReferenceExpression" and n.get("ref"):
            o = owner_req.get(id(n))
            if o is None or not n["ref"].startswith(o + "::"):
                refs_outside[n["ref"]] += 1
        for q in n.get("redef", []) or []:
            redefined[q] += 1
        for q in n.get("chain", []) or []:
            refs_outside[q] += 1

    def tied(qn):
        d = by_qn.get(qn)
        return d is not None and result_expr(d) is not None

    lines = {}
    for g in gates:
        for qn, name, types, mc in g.refs:
            if qn in lines:
                lines[qn]["gates"].add(g.req["qn"])
                continue
            state = "tied" if tied(qn) else "driven" if (refs_outside[qn] or redefined[qn]) else "undriven"
            lines[qn] = dict(name=name, type=types[0] if types else None, state=state, gates={g.req["qn"]})

    # gate classification
    zv = {}

    def var(qn, types):
        if qn not in zv:
            t = types[0] if types else ""
            zv[qn] = Bool(qn) if t.endswith("Boolean") else Int(qn) if t.endswith("Integer") or t.endswith("Natural") \
                else Real(qn)
        return zv[qn]
    gate_rows = []
    for g in gates:
        row = dict(requirement=g.req.get("short") or g.req.get("name"), qn=g.req["qn"],
                   inputs=sorted({q for q, *_ in g.refs}), units=sorted(g.units))
        try:
            f = z3_of(g.node, var)
            consts = []
            for q in row["inputs"]:
                d = by_qn.get(q)
                if d is not None and result_expr(d) is not None:
                    try:
                        consts.append(var(q, d.get("types", [])) == z3_of(result_expr(d), var))
                    except Untranslated:
                        pass
            s = Solver(); s.add(*consts, f)
            can_hold = s.check() == sat
            s = Solver(); s.add(*consts, Not(f))
            can_fail = s.check() == sat
            row["translated"] = True
            row["value"] = "always true" if not can_fail else "always false" if not can_hold else "open"
        except Untranslated as ex:
            row["translated"] = False
            row["value"] = f"not translated ({ex})"
        states = [lines[q]["state"] for q in row["inputs"]]
        row["undriven_inputs"] = states.count("undriven")
        row["driven_inputs"] = states.count("driven")
        row["tied_inputs"] = states.count("tied")
        gate_rows.append(row)

    shared = {q: sorted(v["gates"]) for q, v in lines.items() if len(v["gates"]) > 1}

    # refinement dependencies
    gate_by_req = collections.defaultdict(list)
    for g in gates:
        gate_by_req[g.req["qn"]].append(g)
    kinds = {n["qn"]: n["mc"] for n, _ in nodes if n.get("qn")}
    refs = []
    for n, _ in nodes:
        if n["mc"] == "Dependency" and any(k["mc"] == "MetadataUsage" and k.get("meta") == "ModelingMetadata::Refinement"
                                           for k in n["kids"]):
            for c in n["client"]:
                for s_ in n["supplier"]:
                    ck, sk = kinds.get(c, "?"), kinds.get(s_, "?")
                    if not ck.startswith("Requirement"):
                        why = f"source is not a requirement ({ck})"
                    elif not sk.startswith("Requirement"):
                        why = f"target is not a requirement ({sk})"
                    elif not gate_by_req[c] or not gate_by_req[s_]:
                        why = "no require constraint on " + ("either side" if not gate_by_req[c] and not gate_by_req[s_]
                                                             else "the source" if not gate_by_req[c] else "the target")
                    else:
                        lc = {q for g in gate_by_req[c] for q, *_ in g.refs}
                        ls = {q for g in gate_by_req[s_] for q, *_ in g.refs}
                        why = "checkable" if lc & ls else "no shared line"
                    refs.append(dict(source=c, target=s_, verdict=why))

    # satisfy relations
    sats = []
    for n, _ in nodes:
        if n["mc"] == "SatisfyRequirementUsage":
            binds = [k for k in n["kids"] if k["mc"] in ("AttributeUsage", "ReferenceUsage") and k.get("redef")
                     and result_expr(k) is not None]
            sats.append(dict(requirement=n.get("satisfied"), by=n.get("by"), binds_inputs=len(binds)))

    req_with_gates = {g.req["qn"] for g in gates}
    summary = dict(
        requirement_elements=len(reqs),
        requirement_definitions=sum(1 for r in reqs if r["mc"] == "RequirementDefinition"),
        requirements_with_constraints=len(req_with_gates),
        gates=len(gates),
        gates_translated=sum(1 for r in gate_rows if r["translated"]),
        gate_values=dict(collections.Counter(r["value"] for r in gate_rows)),
        lines=len(lines),
        lines_by_state=dict(collections.Counter(v["state"] for v in lines.values())),
        gates_all_variable_inputs_undriven=sum(1 for r in gate_rows if r["undriven_inputs"] and not r["driven_inputs"]),
        shared_lines=len(shared),
        refinement_dependencies=len(refs),
        refinements_by_verdict=dict(collections.Counter(r["verdict"] for r in refs)),
        satisfy_relations=len(sats),
        satisfy_binding_inputs=sum(1 for s in sats if s["binds_inputs"]),
        units_in_gates=sorted({u for r in gate_rows for u in r["units"]}),
    )
    return dict(summary=summary, gates=gate_rows,
                lines={q: dict(v, gates=sorted(v["gates"])) for q, v in lines.items()},
                shared_lines=shared, refinements=refs, satisfy=sats)


if __name__ == "__main__":
    res = analyse(json.load(open(sys.argv[1])))
    print(json.dumps(res["summary"], indent=1))
    if len(sys.argv) > 2:
        json.dump(res, open(sys.argv[2], "w"), indent=1)
