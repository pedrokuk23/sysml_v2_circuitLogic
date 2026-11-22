#!/usr/bin/env python3
"""sysmlc — a single compiler from SysML v2 (textual subset) to logic.

    python3 -m sysmlc MODEL.sysml [-o OUTDIR] [--no-eda] [--frontend grammar|pilot [--ast DUMP.json]]

Pipeline:  parse -> IR -> z3 semantics -> logic checks (requirements, state machines, ports, variability,
allocation, action flows) -> EDA back end (Verilog; Yosys proofs by SAT / temporal induction; ABC gate counts)
-> logic views (Graphviz) -> results.json + REPORT.md.
"""
import argparse, json, os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from parser import parse
from semantics import Semantics, compile_model, CompileError
import analysis, verilog, views


def report(R, files):
    L = [f"# sysmlc — {os.path.basename(R['model'])}", ""]
    L.append(f"Requirements read: {len(R['requirements'])}. Time: {R['seconds']:.0f} s.")
    cov = R.get("coverage", {})
    L.append("Translation coverage: translated " + ", ".join(f"{k} {v}" for k, v in sorted(cov.get("translated", {}).items()))
             + "; structural only " + ", ".join(f"{k} {v}" for k, v in sorted(cov.get("structural", {}).items()))
             + "; unsupported none; " + f"{cov.get('statements_recognized', 0)} statements, all matched by the subset grammar.")
    for m, M in R.get("machines", {}).items():
        L += ["", f"## Machine `{m}` (enum {M['enum']})", ""]
        L.append(f"- Conflicts (contention): {len(M['contention'])}")
        for c in M["contention"]:
            L.append(f"  - {' × '.join(c['requirements'])}: {c['region'][0]} "
                     f"({c.get('situations_one_step')} situations, {c.get('situations_reachable')} reachable)")
        L.append(f"- Transitions with overlapping guards (where the textual priority matters): "
                 f"{', '.join(' & '.join(p) for p in M.get('overlapping_guards', [])) or 'none'}")
        L.append(f"- Design violates: {', '.join(M['design_violates']) or 'none'} "
                 f"(reachable: {', '.join(M.get('design_violates_reachable', [])) or 'none'})")
        L.append("- Holes per state (one step): " + ", ".join(f"{k} {v['n']}/{v['of']}" for k, v in M["holes"].items()))
        if "holes_reachable" in M:
            L.append(f"- Holes per state (reachable situations only, {M['situations_reachable']} of {M['situations_total']} "
                     "situations reachable): " + ", ".join(f"{k} {v}" for k, v in M["holes_reachable"].items()))
    if R.get("reachability"):
        rr = R["reachability"]
        L += ["", f"Reachable composite states: {rr['n_states']} of {rr['n_states_total']}."]
    for n, c in R.get("port_contracts", {}).items():
        L += ["", f"## Contract `{n}`", "", f"- Asserted: `{c['asserted']}`; projection: `{c['projection']}`; equivalent: {c['equivalent']}"]
        for k, v in c.items():
            if k.startswith("holes_"):
                L.append(f"- {k}: {v['without_contract']} → {v['with_contract']}")
    for y, g in (R.get("output_groups") or {}).items():
        L += ["", f"## Output `{y}` selected by {', '.join(g['requirements'])}", ""]
        L.append(f"- Conflicts (contention): {', '.join(' × '.join(c['requirements']) for c in g['conflicts']) or 'none'}")
        cov = g["coverage"]
        L.append(f"- Holes: {'none' if cov['complete'] else '`' + ' '.join(cov['hole_region'].split()) + '`'}")
        L.append(f"- Overlaps: {', '.join(' & '.join(o['cases']) for o in cov['overlaps']) or 'none'}")
        for k, dp in g["constant_subformulas"].items():
            L.append(f"- {k}: " + "; ".join(f"`{e}` is {w}" for e, w in dp))
    for n, r in (R.get("flowdown") or {}).items():
        L += ["", f"## Refinement `{n}`: {r['original']} ⇐ {', '.join(r['derived'])}", ""]
        wc = r.get("worst_case")
        L.append(f"- Refinement: {'valid' if r['valid'] else 'fails'}; worst case of {r.get('bounded_quantity')}: "
                 f"{wc:.6g}" if wc is not None else f"- Refinement: {'valid' if r['valid'] else 'fails'}")
        for k, a in r["abduction"].items():
            L.append(f"- Replace {k} (over {', '.join(a['vocabulary'])}): `{a['replacement']}` "
                     f"[{a['method']}; {'exists' if a['exists'] else 'none exists' if a['exists'] is False else 'n/a'}]")
        for g, e in r["interfaces"].items():
            if e.get("contract", 1) is None:
                L.append(f"- Interface {g} (shared {', '.join(e['shared'])}): none, {e['note']}")
            else:
                L.append(f"- Interface {g} (shared {', '.join(e['shared'])}): guarantees ≤ {e.get('strongest_bound'):.6g}, "
                         f"tolerated ≤ {e.get('weakest_bound'):.6g}, margin {e.get('margin'):.4g}"
                         if e.get("margin") is not None else f"- Interface {g}: strongest `{e.get('strongest')}`, weakest `{e.get('weakest')}`")
        dd = r["discretisation"]
        L.append(f"- Discretisation: {dd['feasible']} of {dd['of']} combinations of {', '.join(f'{k}: {v}' for k, v in dd['atoms'].items())} "
                 f"are feasible; lemmas {dd['lemmas']}")
    if R.get("parents_one_step"):
        L += ["", "## Parent requirements, one step (z3)", ""]
        L += [f"- {k}: {'valid' if v['valid'] else 'counterexample'}" for k, v in R["parents_one_step"].items()]
    eda = R.get("eda", {})
    if "design" in eda:
        d = eda["design"]
        L += ["", "## EDA: Yosys (temporal induction on the sequential circuit)", "", "| Requirement | Result |", "|---|---|"]
        L += [f"| {k} | {v['result']}{' (k=' + str(v.get('induction_length')) + ')' if v.get('induction_length') else ''} |"
              for k, v in d["properties"].items()]
        for k, v in d["properties"].items():
            if v.get("ic3", {}).get("lemmas"):
                L += ["", f"Inductive invariant found by IC3 for {k} (lemmas the requirement relies on):", ""]
                L += [f"- {x}" for x in v["ic3"]["lemmas"]]
        a, b = d["aig_requirements"], d["aig_design"]
        L += ["", "And-inverter graph (AIG), as written → optimized (Yosys synth + freduce/fraig):",
              f"- requirements (combinational): {a['as_written']['AND']} AND / {a['as_written']['NOT']} NOT → {a['optimized']['AND']} AND / {a['optimized']['NOT']} NOT",
              f"- design (sequential): {b['as_written']['AND']} AND → {b['optimized']['AND']} AND, {b['optimized']['FF']} flip-flops"]
    V = R.get("variability")
    if V:
        L += ["", "## Variability", "", f"- Valid configurations: {V['n_valid']} of {V['n_configs']}",
              f"- Eliminated by each requirement alone: {V.get('eliminated_alone')}", f"- Invalid configurations attributed by unsatisfiable core: {V['invalid_by_core']}", f"- Dead: {V['dead_variants']} ({V['dead_because']})",
              f"- Core: {V['core_variants']}"]
        for k, v in V["revive"].items():
            L.append(f"- Revive {k}: {'possible' if v['possible'] else 'impossible'} — `{v['condition']}`")
        if V["allocation"]:
            bad = [a for a in V["allocation"] if not a["declared_feasible"]]
            L.append(f"- Declared allocation infeasible in {len(bad)} of {len(V['allocation'])} valid configurations")
    if "cfg" in eda:
        c = eda["cfg"]
        L += [f"- Yosys (SAT) proved: {', '.join(k for k in c['proved'])}",
              f"- Configuration circuit (AIG): {c['aig_cfg']['as_written']['AND']} AND as written → {c['aig_cfg']['optimized']['AND']} AND optimized"]
    for a, A in R.get("actions", {}).items():
        L += ["", f"## Actions `{a}`", ""]
        for n, d in A["decisions"].items():
            L.append(f"- {n}: complete={d['complete']} overlaps={d['overlaps']}")
        L.append(f"- Deadlocks: {sum(1 for f in A['flows'] if f['deadlocks'])} valuations; possible loops: {sum(1 for f in A['flows'] if f['loop_possible'])}")
    L += ["", "## Files", ""] + [f"- `{os.path.basename(f)}`" for f in files]
    return "\n".join(L) + "\n"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("model"); ap.add_argument("-o", "--out", default=None); ap.add_argument("--no-eda", action="store_true")
    ap.add_argument("--frontend", choices=("grammar", "pilot"), default="grammar",
                    help="read the model with the subset grammar (default) or through the SysML v2 Pilot "
                         "Implementation's syntax tree (needs the dump of validation/dump_ast.sh)")
    ap.add_argument("--ast", default=None, help="AST dump for --frontend pilot (default results/reference/ast/<model>.json)")
    a = ap.parse_args()
    out = a.out or os.path.splitext(a.model)[0] + "_out"
    os.makedirs(out, exist_ok=True)
    t0 = time.time()
    try:
        if a.frontend == "pilot":
            from pilot_frontend import compile_pilot
            S = compile_pilot(a.model, a.ast)
        else:
            S = compile_model(a.model)
    except Exception as ex:
        from pilot_frontend import PilotFrontendError
        if isinstance(ex, PilotFrontendError):
            ex = CompileError(a.model, [str(ex)])
        elif not isinstance(ex, CompileError):
            raise
        print(str(ex), file=sys.stderr)
        json.dump(dict(model=a.model, status="rejected", errors=ex.errors), open(os.path.join(out, "results.json"), "w"), indent=1)
        sys.exit(2)
    ir = S.ir
    R = analysis.run_all(S)
    R["status"] = "complete"
    R["coverage"] = ir["coverage"]
    if not a.no_eda:
        R["eda"] = {}
        if ir["machines"]:
            R["eda"]["design"] = verilog.prove_design(S, out)
        if R.get("variability"):
            R["eda"]["cfg"] = verilog.prove_cfg(S, R["variability"], out)
    R["seconds"] = time.time() - t0
    files = views.all_views(S, R, out)
    json.dump(R, open(os.path.join(out, "results.json"), "w"), indent=1, ensure_ascii=False, default=str)
    open(os.path.join(out, "REPORT.md"), "w").write(report(R, files))
    print(report(R, files))


if __name__ == "__main__":
    main()
