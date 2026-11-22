#!/usr/bin/env python3
"""Second front end: build the sysmlc intermediate representation from the abstract syntax tree of the SysML v2 Pilot
Implementation instead of from the subset grammar of parser.py.

The Pilot Implementation (release 0.63.1) parses, resolves and validates the model; validation/DumpAst.java writes its
AST as JSON. This module reads that JSON and produces the same IR dictionary as parser.parse, with every expression
printed back, fully parenthesized, from the Pilot's operator tree. compile_pilot() then gives a Semantics object on
which every analysis runs unchanged, so the results can be compared with those of the grammar front end
(tests/run_tests.py, class H; python3 -m sysmlc MODEL --frontend pilot).

The reader is fail-closed in the same sense as the grammar: a construct of the AST that the translation does not
support (an operator outside Table 3, a transition with a trigger or an effect, a requirement with more than one
require constraint, ...) raises PilotFrontendError.
"""
import json, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

OPS = {"implies", "and", "or", "xor", "not", "if", "==", "!=", "<", "<=", ">", ">=", "+", "-", "*", "/"}


class PilotFrontendError(Exception):
    pass


def walk(n):
    yield n
    for k in n["kids"]:
        yield from walk(k)


def is_expr(n):
    return n["mc"].endswith("Expression") or n["mc"].startswith("Literal")


def short(qn):
    return None if qn is None else qn.split("::")[-1].strip("'")


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


def text(n):
    """Pilot expression -> sysmlc expression text, fully parenthesized."""
    mc = n["mc"]
    if mc.startswith("Literal"):
        return n["lit"]
    if mc == "FeatureReferenceExpression":
        if n.get("ref") is None or n.get("refMc", "").endswith("Expression"):
            body = [x for x in n["kids"] if is_expr(x)]
            if len(body) != 1:
                raise PilotFrontendError(f"unexpected body expression in {n.get('qn')}")
            return text(body[0])
        if n["refMc"] == "EnumerationUsage":
            return f"{short(n['refTypes'][0])}::{n['refName']}"
        return n["refName"]
    if mc == "FeatureChainExpression":
        a = args(n)
        tgt = n["targetName"]
        if tgt is None:
            ch = next(k["chain"] for k in n["kids"] if k["mc"] == "Feature" and k.get("chain"))
            tgt = ".".join(short(c) for c in ch)
        return f"{text(a[0])}.{tgt}"
    if mc == "OperatorExpression":
        op, a = n["op"], [text(x) for x in args(n)]
        if op not in OPS:
            raise PilotFrontendError(f"operator '{op}' is outside the translated subset")
        if op == "not":
            return f"(not {a[0]})"
        if op == "if":
            return f"(if {a[0]} ? {a[1]} else {a[2]})"
        if op == "-" and len(a) == 1:
            return f"(- {a[0]})"
        if op == "+" and len(a) == 1:
            return a[0]
        if len(a) != 2:
            raise PilotFrontendError(f"operator '{op}' with {len(a)} operands")
        return f"({a[0]} {op} {a[1]})"
    raise PilotFrontendError(f"expression metaclass {mc} is outside the translated subset")


def ir_from_ast(root, source):
    ir = dict(source=source, enums={}, requirements={}, machines={}, variations={}, asserts={}, system=None,
              actions={}, allocations=[], errors=[], coverage={}, port_defs={}, part_ports={}, ports={},
              subjects=[], part_attrs={}, req_usages={}, derivations={}, connections=[])
    nodes = list(walk(root))
    counts = {}
    for n in nodes:
        counts[n["mc"]] = counts.get(n["mc"], 0) + 1
    ir["coverage"] = {"pilot_ast_elements": counts}
    subjects = set()
    for n in nodes:
        mc = n["mc"]
        if mc == "EnumerationDefinition":
            ir["enums"][n["name"]] = [k["name"] for k in n["kids"] if k["mc"] == "EnumerationUsage"]
        elif mc == "RequirementDefinition":
            cons = [k for k in n["kids"] if k["mc"] == "ConstraintUsage"]
            if len(cons) != 1:
                raise PilotFrontendError(f"requirement '{n['short']}' has {len(cons)} require constraints")
            subj = next((k for k in n["kids"] if k["mc"] == "ReferenceUsage" and k.get("dir") == "in"), None)
            if subj is not None:
                subjects.add(subj["name"])
            doc = next((k.get("body") for k in n["kids"] if k["mc"] == "Documentation"), "") or ""
            ir["requirements"][n["short"]] = dict(
                name=n["name"], doc=" ".join(doc.split()), expr=text(result_expr(cons[0])),
                attrs=[dict(dir=k["dir"], name=k["name"], type=short(k["types"][0])) for k in n["kids"]
                       if k["mc"] == "AttributeUsage" and k.get("dir") in ("in", "out")],
                subject=None if subj is None else
                (subj["name"], None if subj["types"] == ["Base::Anything"] else short(subj["types"][0])))
        elif mc == "RequirementUsage" and n["name"] and n["types"] and \
                all(k["mc"] == "Multiplicity" for k in n["kids"]):
            ir["req_usages"][n["name"]] = short(n["types"][0])
        elif mc == "PortDefinition":
            ir["port_defs"][n["name"]] = [k["name"] for k in n["kids"] if k["mc"] == "AttributeUsage"]
        elif mc == "InterfaceDefinition":
            for k in n["kids"]:
                if k["mc"] == "AssertConstraintUsage":
                    ir["asserts"][k["name"]] = text(result_expr(k))
                if k["mc"] == "PortUsage" and k.get("end"):
                    ty = k["types"][0]
                    conj = bool(re.search(r"'~\w+'$", ty))
                    ir["ports"][k["name"]] = (ty.split("::")[-2] if conj else short(ty), conj)
        elif mc == "PartDefinition":
            if n.get("variation"):
                vs = []
                for v in n["kids"]:
                    if v["mc"] == "PartUsage":
                        vals = {}
                        for a in v["kids"]:
                            if a["mc"] == "AttributeUsage" and a.get("redef"):
                                vals[short(a["redef"][0])] = result_expr(a)["lit"]
                        vs.append((v["name"], vals))
                ir["variations"][n["name"]] = vs
                continue
            ports = {}
            for k in n["kids"]:
                if k["mc"] == "PortUsage":
                    ty = k["types"][0]
                    conj = bool(re.search(r"'~\w+'$", ty))
                    ports[k["name"]] = (ty.split("::")[-2] if conj else short(ty), conj)
                    ir["ports"][k["name"]] = ports[k["name"]]
                elif k["mc"] == "AttributeUsage" and k["name"] and result_expr(k) is None:
                    ir["part_attrs"].setdefault(k["name"], short(k["types"][0]))
                elif k["mc"] in ("ConnectionUsage",):
                    ir["connections"].append(tuple(k["ends"]))
            ir["part_ports"][n["name"]] = ports
            if any(k["mc"] in ("SatisfyRequirementUsage", "AllocationUsage") for k in n["kids"]):
                ir["system"] = dict(
                    name=n["name"],
                    usages={k["name"]: short(k["types"][0]) for k in n["kids"]
                            if k["mc"] == "PartUsage" and k["name"] and k["types"] != ["Parts::Part"]},
                    derived={k["name"]: text(result_expr(k)) for k in n["kids"]
                             if k["mc"] == "AttributeUsage" and k["name"] and result_expr(k) is not None},
                    satisfy=[(k["name"], short(k["types"][0])) for k in n["kids"]
                             if k["mc"] == "SatisfyRequirementUsage" and k["name"]])
                ir["allocations"] = [(k["ends"][0].split(".")[-1], k["ends"][1]) for k in n["kids"]
                                     if k["mc"] == "AllocationUsage"]
        elif mc == "ExhibitStateUsage" or (mc == "StateUsage" and any(k["mc"] == "TransitionUsage" for k in n["kids"])):
            states = [k["name"] for k in n["kids"] if k["mc"] == "StateUsage"]
            init = next(k["ends"][1] for k in n["kids"] if k["mc"] == "SuccessionAsUsage" and k["ends"][0] == "entryAction")
            trans = []
            for k in n["kids"]:
                if k["mc"] == "TransitionUsage":
                    g = [x for x in k["kids"] if is_expr(x)]
                    if len(g) != 1 or any(x["mc"] in ("AcceptActionUsage",) for x in k["kids"]):
                        raise PilotFrontendError(f"transition '{k['name']}': only one guard and no trigger or effect")
                    trans.append(dict(id=k["name"], src=k["src"], guard=text(g[0]), dst=k["dst"]))
            ir["machines"][n["name"]] = dict(states=states, init=init, transitions=trans)
        elif mc == "ActionDefinition":
            kind, edges, attrs = {}, [], {}
            inputs = [k["name"] for k in n["kids"] if k["mc"] == "AttributeUsage" and k.get("dir") == "in"]
            for k in n["kids"]:
                m = {"ActionUsage": "action", "DecisionNode": "decide", "MergeNode": "merge", "ForkNode": "fork",
                     "JoinNode": "join"}.get(k["mc"])
                if m and k["name"]:
                    kind[k["name"]] = m
                    vals = {a["name"]: float(result_expr(a)["lit"]) for a in k["kids"]
                            if a["mc"] == "AttributeUsage" and result_expr(a) is not None}
                    if vals:
                        attrs[k["name"]] = vals
                if k["mc"] == "SuccessionAsUsage":
                    edges.append((k["ends"][0], k["ends"][1], None))
                if k["mc"] == "TransitionUsage":
                    g = [x for x in k["kids"] if is_expr(x)]
                    edges.append((k["src"], k["dst"], text(g[0])))
            for s_, d_, _ in edges:
                for x in (s_, d_):
                    if x not in kind:
                        kind[x] = "start" if x == "start" else "final" if x == "done" else "action"
            ir["actions"][n["name"]] = dict(kind=kind, edges=edges, attrs=attrs, inputs=inputs)
        elif mc == "Dependency":
            meta = [k["meta"] for k in n["kids"] if k["mc"] == "MetadataUsage"]
            if "ModelingMetadata::Refinement" in meta:
                ir["derivations"][n["name"]] = dict(client=[short(c) for c in n["client"]],
                                                    supplier=[short(s) for s in n["supplier"]])
    # interface usages connect ports as well
    for n in nodes:
        if n["mc"] == "InterfaceUsage":
            ir["connections"].append(tuple(n["ends"]))
    names = {r["name"]: k for k, r in ir["requirements"].items()}
    der = {}
    for k, d in ir["derivations"].items():
        der[k] = dict(original=names[ir["req_usages"][d["supplier"][0]]],
                      derived=[names[ir["req_usages"][c]] for c in d["client"]])
    ir["derivations"] = der
    ir["subjects"] = sorted(subjects)
    return ir


def compile_pilot(model_path, ast_path=None):
    """Semantics of a model read through the Pilot Implementation's AST (fail-closed like compile_model)."""
    from semantics import Semantics, CompileError
    if ast_path is None:
        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        ast_path = os.path.join(root, "results", "reference", "ast",
                                os.path.splitext(os.path.basename(model_path))[0] + ".json")
    ir = ir_from_ast(json.load(open(ast_path)), model_path)
    S = Semantics(ir)
    for name, expr in ir["asserts"].items():
        try:
            S.E(expr)
        except Exception as ex:
            S.errors.append(f"assert constraint '{name}': {ex}")
    for aname, a in ir["actions"].items():
        for _, _, g in a["edges"]:
            if g:
                try:
                    S.E(g)
                except Exception as ex:
                    S.errors.append(f"action '{aname}': guard '{g}': {ex}")
    errs = list(S.errors) + [f"name '{n}' is used but not declared" for n in sorted(S.undeclared)]
    if errs:
        raise CompileError(model_path, errs)
    return S
