"""Logic views (Graphviz) generated from the analysis results: requirement circuits per state machine,
port contracts and proofs, configuration circuit, action flow and allocation backbone."""
import os, subprocess, re

RED, GREEN, ORANGE, BLUE, GREY = "#c62828", "#2e7d32", "#e08a00", "#1f5aa6", "#555555"


EN = [("fluxo de ações", "action flow"), ("laço possível em", "possible loop in"), ("impasse em", "deadlock in"), ("Vista lógica — ", "Logic view — "), ("requisitos como lógica de próximo estado", "requirements as next-state logic"),
      ("&amp; = porta E", "&amp; = AND gate"), ("○ = negação", "○ = negation"), ("contenção = conflito", "contention = conflict"),
      ("linha flutuante = lacuna", "floating line = hole"), ("entradas", "inputs"), ("barramento do próximo estado", "next-state bus"),
      ("próximo = ", "next = "), ("CONTENÇÃO", "CONTENTION"), ("estando em ", "in "), (" sem requisito", " unspecified"),
      ("→ SysML: permanece", "→ SysML: stay"), ("contratos de porta e provas (Yosys, indução temporal)", "port contracts and proofs"),
      ("interpolante de Craig = projeção", "Craig interpolant = projection"), ("projeção exata", "exact projection"),
      ("lacunas ", "holes "), ("cada requisito como assert no circuito sequencial (k-indução)", "each requirement as an assertion on the sequential circuit"),
      ("requisito", "requirement"), ("Yosys sat -tempinduct", "result"), ("counterexample", "counterexample"), ("proved", "proved"),
      ("invariante indutivo (IC3/PDR)", "inductive invariant (IC3/PDR)"), ("= lemas que o requirement pressupõe", "= lemmas the requirement relies on"),
      ("variabilidade como circuito de configuração", "variability as a configuration circuit"), ("=1 = exatamente um", "=1 = exactly one"),
      ("vermelho = variante morta", "red = dead variant"), ("verde = variante núcleo", "green = core variant"), ("(Y) = provado no Yosys", "(Y) = proved by SAT in Yosys"),
      (" morta por ", " dead by "), ("reviver via", "revive via"), ("impossível", "impossible"), ("possível", "possible"),
      ("válidas: ", "valid: "), (" de ", " of "), ("valorações", "input valuations"),
      ("ciclo nominal", "nominal cycle (min)"), ("cada laço", "each loop"),
      ("seleção incompleta: And(Not(linkUp), Not(And(linkUp, backlog)))", "incomplete selection: ¬linkUp"),
      ("guardas sobrepostas", "overlapping guards"), ("alocação: espinha dorsal por configuração válida", "allocation backbone per valid configuration"),
      ("viáveis", "feasible"), ("declarada", "declared"), ("livre", "free"), ("(premissa)", "(assumed)"), ("(forçado)", "(forced)"), ("solo ", "ground ")]


def render(outdir, name, lines):
    p = os.path.join(outdir, name)
    txt = "\n".join(lines)
    if os.environ.get("SYSMLC_LANG", "en") == "en":
        for a, b in EN:
            txt = txt.replace(a, b)
    lines = [txt]
    open(p + ".dot", "w").write("\n".join(lines))
    for fmt, dpi in (("svg", 72), ("png", 160)):
        subprocess.run(["dot", f"-T{fmt}", f"-Gdpi={dpi}", p + ".dot", "-o", f"{p}.{fmt}"], check=True)
    return p + ".png"


def gate(n, sym, xl=""):
    x = f', xlabel=<<font point-size="10" color="{GREY}">{xl}</font>>' if xl else ""
    return (f'"{n}" [shape=box, width=0.55, height=0.75, fixedsize=true, label="{sym}", fontsize=15, '
            f'fontname="Helvetica-Bold", style="rounded,filled", fillcolor=white{x}];')


HEAD = ['node [fontname="Helvetica", fontsize=11];', 'fontname="Helvetica";']


def machine_view(S, R, outdir, mname):
    M = R["machines"][mname]
    lits = S.enums[M["enum"]]
    cur = M["cur"]
    L = ['digraph G {', 'rankdir=LR; splines=spline; nodesep=0.25; ranksep=0.9;', *HEAD,
         f'label=<<b>Vista lógica — {mname}: requisitos como lógica de próximo estado</b><br/><font point-size="10">'
         f'&amp; = porta E · ○ = negação · <font color="{RED}">contenção = conflito</font> · '
         f'<font color="{ORANGE}">linha flutuante = lacuna</font></font>>; labelloc=t; fontsize=14;']
    L.append('subgraph cluster_in { label="entradas"; style=dashed; color="#999999"; fontsize=10;')
    for l in lits:
        L.append(f'"{cur}={l}" [shape=plaintext, label="{cur} = {l}"];')
    for s in M["inputs"]:
        L.append(f'"{s}" [shape=plaintext];')
    L.append('}')
    L.append('subgraph cluster_bus { label="barramento do próximo estado"; style=dashed; color="#999999"; fontsize=10;')
    for l in lits:
        L.append(f'"bus_{l}" [shape=cds, style=filled, fillcolor="#e8eef7", color="{BLUE}", label="próximo = {l}"];')
    L.append('}')
    for k in M["requirements"]:
        f = S.R[k]
        g = f"g_{k}"
        L.append(gate(g, "&", k))
        ante = f.arg(0)
        def flat(e):
            return [x for c in e.children() for x in flat(c)] if e.decl().name() == "and" else [e]
        lits_ = flat(ante)
        for lit in lits_:
            neg = lit.decl().name() == "not"
            base = lit.arg(0) if neg else lit
            if base.decl().name() == "=":
                iv = base.arg(1) if base.arg(1).decl().kind() == 2 or str(base.arg(1)).isdigit() else base.arg(0)
                src = f"{cur}={lits[int(str(iv))]}"
            else:
                src = str(base)
            L.append(f'"{src}" -> "{g}" [arrowhead={"odot" if neg else "none"}, color="#444444"];')
        from analysis import target
        L.append(f'"{g}" -> "bus_{lits[target(f)]}" [color="{BLUE}", penwidth=1.6];')
    for c in M["contention"]:
        a, b = c["requirements"]
        n = f"c_{a}_{b}"
        reg = c["region"][0].replace("[", "").replace("]", ":")
        L.append(f'"{n}" [shape=note, style=filled, fillcolor="#fdecea", color="{RED}", fontcolor="{RED}", fontsize=10, '
                 f'label="CONTENÇÃO {a} × {b}\\n{reg}"];')
        L += [f'"g_{a}" -> "{n}" [color="{RED}", style=dashed, arrowhead=none];',
              f'"g_{b}" -> "{n}" [color="{RED}", style=dashed, arrowhead=none];']
    for l, h in M["holes"].items():
        if not h["n"]:
            continue
        reg = h["region"][0].replace("[] ", "")
        L.append(f'"f_{l}" [shape=note, style=filled, fillcolor="#fff4e0", color="{ORANGE}", fontcolor="#8a5200", fontsize=10, '
                 f'label="estando em {l}: {h["n"]}/{h["of"]} sem requisito\\n{reg}\\n→ SysML: permanece"];')
        L.append(f'"bus_{l}" -> "f_{l}" [color="{ORANGE}", style=dotted, arrowhead=none];')
    L.append("}")
    return render(outdir, f"view_{mname}", L)


def proofs_view(S, R, outdir):
    E = R.get("eda", {}).get("design", {})
    props = E.get("properties", {})
    pc = R.get("port_contracts", {})
    L = ['digraph G {', 'rankdir=LR; nodesep=0.3; ranksep=0.7;', *HEAD,
         '''label=<<b>Vista lógica — contratos de porta e provas (Yosys, indução temporal)</b>>; labelloc=t; fontsize=14;''']
    for name, c in pc.items():
        holes = {k: v for k, v in c.items() if k.startswith("holes_")}
        L.append(f'subgraph cluster_{name} {{ label="{name} (interpolante de Craig = projeção)"; style=rounded; color="{BLUE}";')
        sig = sorted({t.split(".")[-1] for t in re.findall(r"[A-Za-z_][\w.]*", c["asserted"])} - {"or", "and", "not"})
        for s in sig:
            L.append(f'"{name}_{s}" [shape=plaintext, label="{s}"];')
        L.append(gate(f"{name}_g", "≥1" if " or " in c["asserted"] else "&"))
        for s in sig:
            L.append(f'"{name}_{s}" -> "{name}_g";')
        txt = "\\n".join(f"{k.replace('holes_', 'holes ')}: {v['without_contract']} → {v['with_contract']}" for k, v in holes.items())
        L.append(f'"{name}_n" [shape=note, style=filled, fillcolor="#e8eef7", color="{BLUE}", label="{c["asserted"]}\\nprojeção exata: {c["equivalent"]}\\n{txt}"];')
        L.append(f'"{name}_g" -> "{name}_n"; }}')
    L.append(f'subgraph cluster_p {{ label="cada requisito como assert no circuito sequencial (k-indução)"; style=rounded; color="{GREEN}";')
    rows = "".join(f'<tr><td align="left">{k}</td><td bgcolor="{"#eaf5ea" if v["result"].startswith("proved") else "#fdecea"}">'
                   f'{v["result"]}{" (k=" + str(v.get("induction_length")) + ")" if v.get("induction_length") else ""}</td></tr>'
                   for k, v in props.items())
    L.append(f'"tbl" [shape=plaintext, label=<<table border="0" cellborder="1" cellspacing="0" cellpadding="4">'
             f'<tr><td bgcolor="#e8eef7"><b>requisito</b></td><td bgcolor="#e8eef7"><b>Yosys sat -tempinduct</b></td></tr>{rows}</table>>]; }}')
    for k, v in props.items():
        lem = v.get("ic3", {}).get("lemmas")
        if lem:
            txt = "\\l".join(lem) + "\\l"
            L.append(f'"lem_{k}" [shape=note, style=filled, fillcolor="#eaf5ea", color="{GREEN}", fontsize=10, '
                     f'label="{k}: invariante indutivo (IC3/PDR)\\n= lemas que o requisito pressupõe\\l{txt}"];')
    L.append("}")
    return render(outdir, "view_provas", L)


def variability_view(S, R, outdir):
    V = R["variability"]
    eda = R.get("eda", {}).get("cfg", {}).get("proved", {})
    reads = {}
    for k, r in S.ir["requirements"].items():
        reads[k] = sorted({u for u in S.usages if re.search(rf"\b{u}\.", r["expr"])} |
                          {u for u in S.usages for d in (S.ir["system"] or {}).get("derived", {}).values() if re.search(rf"\b{u}\.", d)
                           and any(x in r["expr"] for x in (S.ir["system"] or {}).get("derived", {}))})
    if V["allocation_functions"]:
        reads["CAP"] = ["bus"] if "bus" in S.usages else []
    L = ['digraph G {', 'rankdir=LR; nodesep=0.22; ranksep=1.0;', *HEAD,
         f'label=<<b>Vista lógica — variabilidade como circuito de configuração</b><br/><font point-size="10">=1 = exatamente um · '
         f'<font color="{RED}">vermelho = variante morta</font> · <font color="{GREEN}">verde = variante núcleo</font> · '
         f'(Y) = proved in Yosys</font>>; labelloc=t; fontsize=14;']
    for u, vs in V["variations"].items():
        L.append(f'subgraph cluster_{u} {{ label="{u}"; style=dashed; color="#999999"; fontsize=10;')
        for v in vs:
            key = f"{u}.{v}"
            col = RED if key in V["dead_variants"] else GREEN if key in V["core_variants"] else "black"
            y = " (Y)" if eda.get(f"dead:{key}") or eda.get(f"core:{key}") else ""
            L.append(f'"{key}" [shape=plaintext, label="{v}{y}", fontcolor="{col}"];')
        L.append("}")
        L.append(gate(f"oh_{u}", "=1"))
        L += [f'"{u}.{v}" -> "oh_{u}" [arrowhead=none];' for v in vs]
    for r, us in reads.items():
        L.append(f'"{r}" [shape=box, style="rounded,filled", fillcolor="#e8eef7", color="{BLUE}", label="{r}"];')
        L += [f'"oh_{u}" -> "{r}" [color="#666666"];' for u in us]
    L.append(gate("valid", "&"))
    L += [f'"{r}" -> "valid" [color="{BLUE}"];' for r in reads]
    L.append(f'"out" [shape=note, style=filled, fillcolor="#eaf5ea", color="{GREEN}", label="válidas: {V["n_valid"]} de {V["n_configs"]}"];')
    L.append('"valid" -> "out";')
    for dv, core in V["dead_because"].items():
        rv = [v for k, v in V["revive"].items() if k.startswith(dv)]
        extra = "\\n".join(f"reviver via {', '.join(x['free'])}: {'possível' if x['possible'] else 'impossível'}" for x in rv)
        L.append(f'"dn_{dv}" [shape=note, style=filled, fillcolor="#fdecea", color="{RED}", fontcolor="{RED}", fontsize=10, '
                 f'label="{dv} morta por {" + ".join(core)}\\n{extra}"];')
        L.append(f'"{dv}" -> "dn_{dv}" [color="{RED}", style=dashed, arrowhead=none];')
    L.append("}")
    return render(outdir, "view_variabilidade", L)


def action_view(S, R, outdir, aname):
    A = R["actions"][aname]
    L = ['digraph G {', 'rankdir=LR; nodesep=0.35; ranksep=0.55;', *HEAD,
         f'label=<<b>Vista lógica — fluxo de ações {aname}</b><br/><font point-size="10">decide = MUX · join = &amp; · merge = ≥1</font>>; labelloc=t; fontsize=14;']
    bad_dec = {n for n, d in A["decisions"].items() if not d["complete"] or d["overlaps"]}
    for n, k in A["nodes"].items():
        if k == "start":
            L.append(f'"{n}" [shape=circle, style=filled, fillcolor=black, label="", width=0.25];')
        elif k == "final":
            L.append(f'"{n}" [shape=doublecircle, style=filled, fillcolor=black, label="", width=0.2];')
        elif k == "decide":
            col = RED if n in bad_dec else "black"
            L.append(f'"{n}" [shape=invtrapezium, label="MUX\\n{n}", color="{col}", fontcolor="{col}"];')
        elif k in ("fork", "join"):
            L.append(f'"{n}" [shape=box, style=filled, fillcolor=black, fontcolor=white, width=0.15, height=1.0, fixedsize=true, label="{"&" if k == "join" else ""}"];')
        elif k == "merge":
            L.append(f'"{n}" [shape=diamond, label="≥1", fontsize=10, width=0.5, height=0.5, fixedsize=true];')
        else:
            L.append(f'"{n}" [shape=box, style=rounded];')
    for s, t, g in A["edges"]:
        L.append(f'"{s}" -> "{t}"' + (f' [label="[{g}]", fontsize=10]' if g else "") + ";")
    for n, d in A["decisions"].items():
        msg = []
        if not d["complete"]:
            msg.append(f"seleção incompleta: {d['hole']}")
        if d["overlaps"]:
            msg.append("guardas sobrepostas: " + "; ".join(" & ".join(o) for o in d["overlaps"]))
        if msg:
            L.append(f'"note_{n}" [shape=note, style=filled, fillcolor="#fdecea", color="{RED}", fontcolor="{RED}", fontsize=10, label="{n}\\n' + "\\n".join(msg) + '"];')
            L.append(f'"{n}" -> "note_{n}" [color="{RED}", style=dashed, arrowhead=none];')
    dl = [f for f in A["flows"] if f["deadlocks"]]
    lp = [f for f in A["flows"] if f["loop_possible"]]
    txt = f"impasse em {len(dl)} de {len(A['flows'])} valorações\\nlaço possível em {len(lp)}\\nciclo nominal: {A['nominal_cycle_min']:.0f}; cada laço: +{max(A['loops'].values()) if A['loops'] else 0:.0f}"
    L.append(f'"summary" [shape=note, style=filled, fillcolor="#fff4e0", color="{ORANGE}", label="{txt}"];')
    L.append("}")
    return render(outdir, f"view_acoes_{aname}", L)


def allocation_view(S, R, outdir):
    V = R["variability"]
    funs = V["allocation_functions"]
    keys = list(V["variations"])
    hdr = "".join(f'<td bgcolor="#e8eef7"><b>{h}</b></td>' for h in keys + funs + ["viáveis", "declarada"])
    rows = []
    for a in V["allocation"]:
        cells = "".join(f"<td>{a['config'][k]}</td>" for k in keys)
        for f in funs:
            if f in a["fixed"]:
                cells += '<td bgcolor="#eeeeee">OBC (premissa)</td>'
            elif f in a["forced"]:
                cells += f'<td bgcolor="#eaf5ea"><b>{a["forced"][f]} (forçado)</b></td>'
            else:
                cells += "<td>livre</td>"
        cells += f"<td>{a['feasible_allocations']}</td>"
        cells += f'<td bgcolor="{"#eaf5ea" if a["declared_feasible"] else "#fdecea"}">{"✓" if a["declared_feasible"] else "✗"}</td>'
        rows.append(f"<tr>{cells}</tr>")
    L = ['digraph G {', *HEAD, '''label=<<b>Vista lógica — alocação: espinha dorsal por configuração válida</b>>; labelloc=t; fontsize=14;''',
         f'"t" [shape=plaintext, label=<<table border="0" cellborder="1" cellspacing="0" cellpadding="5"><tr>{hdr}</tr>{"".join(rows)}</table>>];', "}"]
    return render(outdir, "view_alocacao", L)


def all_views(S, R, outdir):
    out = []
    for m in R.get("machines", {}):
        out.append(machine_view(S, R, outdir, m))
    if R.get("machines"):
        out.append(proofs_view(S, R, outdir))
    if R.get("variability"):
        out.append(variability_view(S, R, outdir))
        if R["variability"]["allocation"]:
            out.append(allocation_view(S, R, outdir))
    for a in R.get("actions", {}):
        out.append(action_view(S, R, outdir, a))
    return out
