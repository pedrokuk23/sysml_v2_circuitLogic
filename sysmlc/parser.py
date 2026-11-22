"""SysML v2 textual subset -> intermediate representation (IR).

Elements read: enum def; requirement def (doc, typed in/out attributes, require
constraint); part def with attributes (derived values), ports, exhibit state (guarded transitions), allocate,
perform; variation part def / variant part with redefined attribute values; interface def with assert constraint;
action def with first/then/decide/fork/merge/join/if successions and per-action attributes.
Comments (// ...) are stripped. Block comments are kept only as 'doc'.

The parser is fail-closed: duplicated identifiers, malformed transitions or variants, several or no require
constraints in a requirement, and SysML constructs whose semantics the compiler does not translate are reported in
ir["errors"]; constructs that carry no behavior for the analysis (packages, imports, part usages, satisfy, ports)
are listed in ir["coverage"]. The driver stops before any analysis when ir["errors"] is not empty.
"""
import re


def block(text, start):
    i = text.index("{", start); depth = 0
    for j in range(i, len(text)):
        depth += text[j] == "{"; depth -= text[j] == "}"
        if depth == 0:
            return text[i + 1:j], j
    raise ValueError("unbalanced braces")


def strip_comments(t):
    return re.sub(r"//[^\n]*", "", t)


def norm(s):
    return " ".join(s.split())


def parse(path):
    raw = open(path).read()
    t = strip_comments(raw)
    ir = dict(source=path, enums={}, requirements={}, machines={}, variations={}, asserts={},
              system=None, actions={}, allocations=[], errors=[], coverage={})
    err = ir["errors"]

    def put(kind, key, value):
        if key in ir[kind]:
            err.append(f"duplicate {kind[:-1] if kind.endswith('s') else kind} identifier '{key}'")
        ir[kind][key] = value
    for e in re.finditer(r"enum def (\w+)\s*\{([^}]*)\}", t):
        lits = re.findall(r"enum (\w+);", e.group(2))
        if len(set(lits)) != len(lits):
            err.append(f"duplicate literal in enum '{e.group(1)}'")
        put("enums", e.group(1), lits)
    for r in re.finditer(r"requirement def <'([^']+)'>\s*(\w+)", t):
        body, _ = block(t, r.end())
        doc = re.search(r"doc\s*/\*(.*?)\*/", body, re.S)
        nreq = len(re.findall(r"\brequire constraint\b", body))
        if nreq != 1:
            err.append(f"requirement '{r.group(1)}' has {nreq} require constraints (exactly one is supported)")
            continue
        if re.search(r"\bassume constraint\b", body):
            err.append(f"requirement '{r.group(1)}' has an assume constraint (not supported; write it as an antecedent)")
        e, _ = block(body, re.search(r"require constraint", body).end())
        attrs = [dict(dir=a.group(1), name=a.group(2), type=a.group(3))
                 for a in re.finditer(r"\b(in|out)\s+attribute (\w+)\s*:\s*(\w+)", body)]
        names = [a["name"] for a in attrs]
        if len(set(names)) != len(names):
            err.append(f"requirement '{r.group(1)}' declares an attribute twice")
        put("requirements", r.group(1), dict(name=r.group(2), doc=norm(doc.group(1)) if doc else "",
                                             expr=norm(e), attrs=attrs))
    for s in re.finditer(r"exhibit state (\w+)", t):
        body, _ = block(t, s.end())
        states = re.findall(r"\bstate (\w+);", body)
        init = re.search(r"entry;\s*then (\w+);", body)
        trans = [dict(id=x.group(1), src=x.group(2), guard=norm(x.group(3)), dst=x.group(4))
                 for x in re.finditer(r"transition (\w+) first (\w+) if (.+?) then (\w+);", body, re.S)]
        ntrans = len(re.findall(r"\btransition\b", body))
        if ntrans != len(trans):
            err.append(f"machine '{s.group(1)}': {ntrans - len(trans)} transition(s) not of the form "
                       "'transition t first A if guard then B;' (triggers, effects and timed transitions are not supported)")
        if re.search(r"\b(entry|exit|do)\s+action\b|\baccept\b|\bsend\b|\bafter\b|\bwhen\b", body):
            err.append(f"machine '{s.group(1)}': entry/exit/do actions, accept/send or time triggers are not supported")
        if len(set(states)) != len(states):
            err.append(f"machine '{s.group(1)}': duplicate state")
        ids = [x["id"] for x in trans]
        if len(set(ids)) != len(ids):
            err.append(f"machine '{s.group(1)}': duplicate transition identifier")
        for x in trans:
            for st in (x["src"], x["dst"]):
                if st not in states:
                    err.append(f"machine '{s.group(1)}': transition '{x['id']}' refers to undeclared state '{st}'")
        if not init or init.group(1) not in states:
            err.append(f"machine '{s.group(1)}': missing or invalid initial state ('entry; then S;')")
            continue
        put("machines", s.group(1), dict(states=states, init=init.group(1), transitions=trans))
    for v in re.finditer(r"variation part def (\w+)", t):
        body, _ = block(t, v.end())
        if len(re.findall(r"\bvariant\b", body)) != len(re.findall(r"variant part (\w+)\s*:\s*\w+\s*\{([^}]*)\}", body)):
            err.append(f"variation '{v.group(1)}': variant not of the form 'variant part v : T {{ attribute redefines x = value; }}'")
        put("variations", v.group(1), [
            (x.group(1), dict(re.findall(r"attribute redefines (\w+)\s*=\s*([\w.]+);", x.group(2))))
            for x in re.finditer(r"variant part (\w+)\s*:\s*\w+\s*\{([^}]*)\}", body)])
    for a in re.finditer(r"assert constraint (\w+)", t):
        body, _ = block(t, a.end())
        put("asserts", a.group(1), norm(body))
    # the system part: the part def that holds variation usages, allocations or satisfy relations
    for p in re.finditer(r"part def (\w+)\s*\{", t):
        body, _ = block(t, p.start())
        if re.search(r"\b(satisfy|allocate)\b", body):
            if ir["system"]:
                err.append(f"two system parts ('{ir['system']['name']}' and '{p.group(1)}') hold satisfy or allocate "
                           "relations; exactly one is supported")
            ir["system"] = dict(
                name=p.group(1),
                usages=dict(re.findall(r"part (\w+)\s*:\s*(\w+);", body)),
                derived={m.group(1): norm(m.group(2)) for m in re.finditer(r"attribute (\w+)\s*:\s*\w+\s*=\s*(.+?);", body)},
                satisfy=re.findall(r"satisfy requirement (\w+)\s*:\s*(\w+)", body))
            ir["allocations"] = re.findall(r"allocate (?:\w+\.)?(\w+) to (\w+);", body)
    # ports, port definitions, connections and subjects: read for structure and checked for consistency
    ir["port_defs"] = {}
    for d in re.finditer(r"port def (\w+)", t):
        body, _ = block(t, d.end())
        ir["port_defs"][d.group(1)] = [m.group(2) for m in re.finditer(r"\b(in|out) attribute (\w+)", body)]
    ir["part_ports"] = {}
    for p in re.finditer(r"part def (\w+)\s*\{", t):
        body, _ = block(t, p.start())
        ir["part_ports"][p.group(1)] = {m.group(1): (m.group(3), bool(m.group(2)))
                                        for m in re.finditer(r"\bport (\w+)\s*:\s*(~)?(\w+);", body)}
    # signals are resolved by name, so a port name must denote one port in the whole model
    owners = [(n, v, f"part def '{part}'") for part, pp in ir["part_ports"].items() for n, v in pp.items()]
    owners += [(e.group(1), (e.group(3), bool(e.group(2))), "an interface end")       # interface ends act as ports
               for e in re.finditer(r"\bend (\w+)\s*:\s*(~)?(\w+);", t)]
    ir["ports"] = {}
    for n, v, where in owners:
        if n in ir["ports"]:
            err.append(f"port name '{n}' is declared more than once (in {where}); port names must be unique in the "
                       "model because signals are resolved by name")
        ir["ports"][n] = v
    for e in re.finditer(r"\bend (\w+)\s*:\s*(~)?(\w+);", t):
        if e.group(3) not in ir["port_defs"]:
            ir["errors"].append(f"interface end '{e.group(1)}' is typed by undeclared port definition '{e.group(3)}'")
    ir["subjects"] = sorted(set(re.findall(r"\bsubject (\w+)", t)))
    ir["connections"] = re.findall(r"\bconnect ([\w.]+) to ([\w.]+);", t)
    for a in re.finditer(r"action def (\w+)", t):
        body, _ = block(t, a.end())
        put("actions", a.group(1), parse_action(body))
    coverage(t, ir)
    consumed(raw, ir)
    check_structure(ir)
    return ir


def check_structure(ir):
    """Ports, port definitions and connections are not translated (signals are identified by name), but they must
    be consistent: ports typed by declared port definitions, connections between declared ports of declared part
    usages, and the two ends of a connection typed by the same port definition, one of them conjugated (~)."""
    err = ir["errors"]
    for part, ports in ir["part_ports"].items():
        for name, (pdef, _) in ports.items():
            if pdef not in ir["port_defs"]:
                err.append(f"port '{name}' of part '{part}' is typed by undeclared port definition '{pdef}'")
    usages = (ir["system"] or {}).get("usages", {})
    for a, b in ir["connections"]:
        ends = []
        for e in (a, b):
            seg = e.split(".")
            if len(seg) != 2 or seg[0] not in usages or seg[1] not in ir["part_ports"].get(usages[seg[0]], {}):
                err.append(f"connection end '{e}' is not a declared port of a part usage"); break
            ends.append(ir["part_ports"][usages[seg[0]]][seg[1]])
        if len(ends) == 2 and (ends[0][0] != ends[1][0] or ends[0][1] == ends[1][1]):
            err.append(f"connection '{a}' to '{b}' joins ports that are not conjugate ({ends[0]} and {ends[1]})")


# ------------------------------------------------------------------ full-consumption check
# Every statement of the model must match one rule of this grammar, in the context where it appears; anything
# else (an unknown keyword, a misplaced element, a stray token) is an error. Each rule is
#   (regex for the whole statement header, context of its body or EXPR or None for 'no body', body allowed?)
# EXPR bodies are expressions; they are parsed by the strict expression parser in semantics.py.
_I, _P = r"\w+", r"[\w.]+"
EXPR = "expr"
_D = r"(?P<n>\w+)"          # the name a statement declares in its scope (checked for duplicates)
GRAMMAR = {
    "top": [(rf"package {_D}", "package", "required")],
    "package": [
        (rf"(private |public )?import [\w:]+(::\*)?", None, "none"),
        (rf"enum def {_D}", "enum", "required"),
        (rf"requirement def (?P<id><'[^']+'>) {_D}", "requirement", "required"),
        (rf"requirement {_D} : {_I}", None, "none"),
        (rf"part def {_D}", "part", "required"),
        (rf"part {_D} : {_I}", None, "none"),
        (rf"port def {_D}", "port", "required"),
        (rf"interface def {_D}", "interface", "required"),
        (rf"variation part def {_D}( :> {_I})?", "variation", "required"),
        (rf"action def {_D}", "action", "required"),
        (rf"satisfy (requirement )?{_I}( : {_I})? by {_P}", None, "none")],
    "enum": [(rf"enum {_D}", None, "none")],
    "requirement": [
        (r"doc", None, "none"),
        (rf"subject {_D}( : {_I})?", None, "none"),
        (rf"(in|out) attribute {_D} : {_I}", None, "none"),
        (r"require constraint", EXPR, "required")],
    "part": [
        (rf"(in |out )?attribute {_D} : {_I}( = .+)?", None, "none"),
        (rf"part {_D}( : {_I})?", None, "none"),
        (rf"port {_D} : ~?{_I}", None, "none"),
        (rf"connect {_P} to {_P}", None, "none"),
        (rf"interface {_D} : {_I} connect {_P} to {_P}", None, "none"),
        (rf"exhibit state {_D}", "machine", "required"),
        (rf"allocate {_P} to {_I}", None, "none"),
        (rf"perform action {_D} : {_I}", None, "none"),
        (rf"satisfy (requirement )?{_I}( : {_I})? by {_P}", None, "none")],
    "port": [(rf"(in|out) attribute {_D} : {_I}", None, "none")],
    "interface": [
        (rf"end {_D} : ~?{_I}", None, "none"),
        (rf"assert constraint {_D}", EXPR, "required")],
    "machine": [
        (r"entry", None, "none"),
        (rf"then {_I}", None, "none"),
        (rf"state {_D}", None, "none"),
        (rf"transition {_D} first {_I} if .+ then {_I}", None, "none")],
    "variation": [(rf"variant part {_D} : {_I}", "variant", "required")],
    "variant": [(rf"attribute redefines {_D} = [\w.]+", None, "none")],
    "action": [
        (rf"in attribute {_D} : Boolean", None, "none"),
        (rf"first {_I}", None, "none"),
        (rf"then (action|decide|fork|merge|join) {_D}", "step", "optional"),
        (rf"then {_I}", "step", "optional"),
        (rf"(action|decide|fork|merge|join) {_D}", "step", "optional"),
        (rf"if .+ then {_I}", None, "none")],
    "step": [(rf"attribute {_D} : Real = [\d.]+", None, "none")],
}


def _statements(t, off=0):
    """Split a body into (header, body or None, start, end) at depth 0; start and end delimit the whole statement
    (header, body and terminator) in the enclosing text, shifted by off. A trailing fragment without ';' or '{...}'
    is returned with body '<unterminated>'."""
    out, i, start, n = [], 0, 0, len(t)
    while i < n:
        c = t[i]
        if c == ";":
            out.append((t[start:i], None, off + start, off + i + 1)); start = i + 1
        elif c == "{":
            d, j = 0, i
            while j < n:
                d += t[j] == "{"; d -= t[j] == "}"
                if d == 0:
                    break
                j += 1
            if d:
                out.append((t[start:i], "<unbalanced>", off + start, off + n)); return out
            out.append((t[start:i], (t[i + 1:j], off + i + 1), off + start, off + j + 1)); i = j; start = j + 1
        elif c == "}":
            out.append((t[start:i], "<unbalanced>", off + start, off + i)); return out
        i += 1
    if t[start:].strip():
        out.append((t[start:], "<unterminated>", off + start, off + n))
    return out


def _blank(m):
    return re.sub(r"[^\n]", " ", m.group(0))


def clean(text):
    """Remove comments without moving any character: '// ...' and '/* ... */' become blanks and a documentation
    comment 'doc /* ... */' becomes the statement 'doc;' padded with blanks."""
    text = re.sub(r"//[^\n]*", _blank, text)
    text = re.sub(r"\bdoc\s*/\*.*?\*/", lambda m: "doc;" + _blank(m)[4:], text, flags=re.S)
    return re.sub(r"/\*.*?\*/", _blank, text, flags=re.S)


def walk_model(text):
    """Match every statement of the model against GRAMMAR. Returns (errors, number of statements recognized,
    declarations), where each declaration is (start, end, context, name) in the original text."""
    t = clean(text)
    errors, decls, n_ok = [], [], [0]

    def walk(body, off, ctx, where):
        names = {}                                 # one namespace per body: every declared name must be unique
        for head, sub, s0, s1 in _statements(body, off):
            h = norm(head)
            if not h and sub is None:
                continue                                              # empty statement ';'
            if sub in ("<unbalanced>", "<unterminated>"):
                errors.append(f"{sub[1:-1]} text in {where}: '{h[:60]}'"); continue
            for rx, child, b in GRAMMAR[ctx]:
                m = re.fullmatch(rx, h)
                if m and (b == "optional" or (b == "required") == (sub is not None)):
                    n_ok[0] += 1
                    for key in ("n", "id"):
                        nm = m.groupdict().get(key)
                        if nm:
                            if nm in names:
                                errors.append(f"duplicate declaration of '{nm}' in {where}: "
                                              f"'{names[nm][:40]}' and '{h[:40]}'")
                            names[nm] = h
                            decls.append((s0, s1, ctx, nm))
                    if sub is not None and child not in (None, EXPR):
                        walk(sub[0], sub[1], child, f"{ctx} '{h[:40]}'")
                    break
            else:
                errors.append(f"unrecognized statement in {where}: '{h[:60]}{' {...}' if sub is not None else ''}'"
                              " (not in the supported subset)")
    walk(t, 0, "top", "the model")
    return errors, n_ok[0], decls


def consumed(text, ir):
    errors, n, _ = walk_model(text)
    ir["errors"] += errors
    ir["coverage"]["statements_recognized"] = n


# Constructs the compiler translates, constructs it reads but that carry no behavior for the analysis, and
# constructs that would change the meaning of the model but are not translated (these make the compilation fail).
TRANSLATED = ["enum def", "requirement def", "require constraint", "exhibit state", "transition", "variation part def",
              "variant part", "assert constraint", "action def", "decide", "fork", "merge", "join", "allocate",
              "attribute"]
STRUCTURAL = ["package", "import", "part def", "part", "satisfy", "subject", "doc", "port def", "port", "interface def",
              "end", "perform action", "requirement", "item def", "connection def", "connect", "interface"]
UNSUPPORTED = ["assume constraint", "constraint def", "calc def", "analysis def", "verification def", "use case def",
               "occurrence def", "flow", "succession", "bind", "accept", "send", "entry action",
               "exit action", "do action", "timeslice", "snapshot", "individual", "message", "exhibit state def",
               "state def", "until", "loop", "while", "for "]


def coverage(t, ir):
    body = re.sub(r"/\*.*?\*/", " ", t, flags=re.S)
    body = re.sub(r"<'[^']*'>", " ", body)
    cov = {}
    allk = [(k.strip(), g) for g, kws in (("translated", TRANSLATED), ("structural", STRUCTURAL),
                                          ("unsupported", UNSUPPORTED)) for k in kws]
    for k, group in sorted(allk, key=lambda x: -len(x[0])):      # longest keyword first, each match counted once
        pat = r"(?<![\w.])" + re.escape(k) + r"\b"
        n = len(re.findall(pat, body))
        if n:
            cov.setdefault(group, {})[k] = n
            body = re.sub(pat, " ", body)
    ir["coverage"] = cov
    for k, n in cov.get("unsupported", {}).items():
        ir["errors"].append(f"unsupported construct '{k}' ({n} occurrence(s)): its semantics is not translated")


def parse_action(body):
    attrs = {a.group(1): {k: float(v) for k, v in re.findall(r"attribute (\w+)\s*:\s*Real\s*=\s*([\d.]+);", a.group(2))}
             for a in re.finditer(r"action (\w+)\s*\{([^}]*)\}", body)}
    inputs = re.findall(r"in attribute (\w+)\s*:\s*Boolean;", body)
    flat = re.sub(r"\{[^}]*\}", ";", body)
    kind, edges, cur = {}, [], None
    for raw in flat.split(";"):
        l = norm(raw)
        if not l or l.startswith("in attribute"):
            continue
        m = re.match(r"first (\w+)$", l)
        if m:
            cur = m.group(1); kind[cur] = "start"; continue
        m = re.match(r"then (?:action )?(decide|fork|merge|join)? ?(\w+)$", l)
        if m:
            k, n = m.group(1), m.group(2)
            kind.setdefault(n, k or "action")
            edges.append((cur, n, None))
            if kind.get(cur) != "fork" or k:
                cur = n
            continue
        m = re.match(r"if (.+) then (\w+)$", l)
        if m:
            edges.append((cur, m.group(2), m.group(1))); kind.setdefault(m.group(2), "action"); continue
        m = re.match(r"(action|merge|join|decide|fork) (\w+)$", l)
        if m:
            cur = m.group(2); kind[cur] = m.group(1)
    if "done" in kind:
        kind["done"] = "final"
    return dict(kind=kind, edges=edges, attrs=attrs, inputs=inputs)
