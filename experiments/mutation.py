#!/usr/bin/env python3
"""Defect-injection (mutation) experiment on the Lockheed Martin requirement set.

Each mutant changes ONE requirement constraint (FSM-002 .. FSM-013) of the original set (models/lmcps_fsm.sysml) or
of the revised set (--model models/lmcps_fsm_rev.sysml). Three operators mimic editing errors and change the meaning:
  drop     remove one conjunct of the antecedent;
  negate   negate one literal of the antecedent;
  retarget change the target state literal of the consequent.
Three operators rewrite the text without changing the meaning (refactorings), so a textual diff flags them while the
miter must report equivalence:
  reorder  reverse the order of the conjuncts of the antecedent;
  demorgan write the antecedent  a and b and ...  as  not (not a or not b or ...);
  dneg     write one literal  c  as  not (not c).
For each mutant we record:
  miter    sysmlc semantic difference against the original: equivalent or not, the number of valuations where the
           two versions differ (exact), and the logical order (weaker / stronger / incomparable);
  circuit  change in conflicts (bus contention) and holes (undriven lines) of the state-machine circuit, and the
           exact region where the design violates the mutated requirement;
  ic3      IC3/PDR (z3 Spacer) proof of the mutated requirement over the states reachable from the initial state;
  kind2    Kind 2 model-checking verdict of the mutated requirement against the same state-machine design
           (one property per requirement; on a violation Kind 2 returns one counterexample trace).

    KIND2=/path/to/kind2 Z3_BIN=/path/to/z3 python3 experiments/mutation.py [-o results/out/mutation]
"""
import argparse, itertools, json, os, re, sys, tempfile, time
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import And, Xor, Implies, BoolVal, IntVal, substitute, simplify, is_true  # noqa: E402
from semantics import compile_model  # noqa: E402
from logic_engine import valid  # noqa: E402
import analysis, lustre, ic3  # noqa: E402

MODEL = os.path.join(ROOT, "models", "lmcps_fsm.sysml")
IDS = [f"FSM-{i:03d}" for i in range(2, 14)]
PAT = re.compile(r"require constraint \{ \((.*?)\) implies (\w+) == (\w+)::(\w+) \}")


def mutants(text, enums):
    out = []
    for rid in IDS:
        start = text.index(f"requirement def <'{rid}'>")
        m = PAT.search(text, start)
        ante, nxt, enum, lit = m.group(1), m.group(2), m.group(3), m.group(4)
        conj = [c.strip() for c in ante.split(" and ")]

        def put(new_ante, new_lit, op, what):
            new = f"require constraint {{ ({new_ante}) implies {nxt} == {enum}::{new_lit} }}"
            out.append(dict(id=f"{rid}:{op}:{len(out)}", req=rid, op=op, change=what,
                            text=text[:m.start()] + new + text[m.end():]))
        if len(conj) > 1:
            for i, c in enumerate(conj):
                put(" and ".join(conj[:i] + conj[i + 1:]), lit, "drop", f"drop '{c}'")
        for i, c in enumerate(conj):
            if " == " in c:
                n = c.replace(" == ", " != ")
            elif c.startswith("not "):
                n = c[4:]
            else:
                n = "not " + c
            put(" and ".join(conj[:i] + [n] + conj[i + 1:]), lit, "negate", f"'{c}' -> '{n}'")
        for other in enums[enum]:
            if other != lit:
                put(ante, other, "retarget", f"{enum}::{lit} -> {enum}::{other}")
        if len(conj) > 1:
            put(" and ".join(reversed(conj)), lit, "reorder", "reverse conjuncts")
            put("not (" + " or ".join(f"not ({c})" if " " in c else f"not {c}" for c in conj) + ")", lit, "demorgan",
                "De Morgan")
        for i, c in enumerate(conj):
            put(" and ".join(conj[:i] + [f"not (not ({c}))"] + conj[i + 1:]), lit, "dneg", f"'{c}' -> 'not (not ({c}))'")
    return out


def count_diff(So, Sn, k):
    """Exact number of valuations of the requirement's variables (current state, inputs, next state) where the
    original and mutated requirement disagree."""
    f, g = So.R[k], Sn.R[k]
    names = sorted(set(re.findall(r"[A-Za-z_]\w*", str(f) + " " + str(g))) & set(So.vars))
    ranges = [range(len(So.enums[So.vtype[n]])) if So.vtype.get(n) in So.enums else (False, True) for n in names]
    n_diff = 0
    for vals in itertools.product(*ranges):
        val = [BoolVal(v) if isinstance(v, bool) else IntVal(v) for v in vals]
        fo = simplify(substitute(f, *[(So.vars[n], e) for n, e in zip(names, val)]))
        fn = simplify(substitute(g, *[(Sn.vars[n], e) for n, e in zip(names, val)]))
        if is_true(fo) != is_true(fn):
            n_diff += 1
    total = 1
    for r in ranges:
        total *= len(r)
    return n_diff, total, names


def circuit_summary(S):
    R = analysis.check_machines(S)
    return dict(conflicts=sorted(tuple(c["requirements"]) for v in R.values() for c in v["contention"]),
                holes=sum(h["n"] for v in R.values() for h in v["holes"].values()),
                violates={k: reg for v in R.values() for k, reg in v["design_violates"].items()})


def main():
    ap = argparse.ArgumentParser(); ap.add_argument("-o", "--out", default=os.path.join(os.environ.get("OUT", "results/out"), "mutation"))
    ap.add_argument("--model", default=MODEL)
    a = ap.parse_args(); os.makedirs(a.out, exist_ok=True)
    text = open(a.model).read()
    So = compile_model(a.model)
    base = circuit_summary(So)
    have_kind2 = os.path.exists(lustre.KIND2) or bool(os.environ.get("KIND2"))
    kbase = {}
    ic3_base = {k: ic3.prove(So, k)["result"] for k in IDS}
    if have_kind2:
        p = os.path.join(a.out, "orig.lus"); lustre.emit(So, p); kbase, _, _ = lustre.check(p)
    rows = []
    MS = mutants(text, So.enums)
    for i, mu in enumerate(MS):
        path = os.path.join(a.out, f"m{i:03d}.sysml"); open(path, "w").write(mu["text"])
        Sn = compile_model(path)
        k = mu["req"]
        dom = And(So.domain, Sn.domain)
        eq = valid(So.R[k] == Sn.R[k], dom)[0]
        nd, tot, names = count_diff(So, Sn, k)
        order = ("equivalent" if eq else "stronger" if valid(Implies(Sn.R[k], So.R[k]), dom)[0]
                 else "weaker" if valid(Implies(So.R[k], Sn.R[k]), dom)[0] else "incomparable")
        t0 = time.time(); cs = circuit_summary(Sn); t_circ = time.time() - t0
        row = dict(id=mu["id"], req=k, op=mu["op"], change=mu["change"], miter_equivalent=eq, differing_valuations=nd,
                   valuations=tot, variables=names, order=order,
                   conflicts_added=[c for c in cs["conflicts"] if c not in base["conflicts"]],
                   conflicts_removed=[c for c in base["conflicts"] if c not in cs["conflicts"]],
                   holes_delta=cs["holes"] - base["holes"],
                   design_violates_before=k in base["violates"], design_violates_after=k in cs["violates"],
                   violation_region=cs["violates"].get(k), circuit_seconds=round(t_circ, 2))
        t0 = time.time(); pr = ic3.prove(Sn, k)
        row["ic3_before"] = ic3_base[k]
        row.update(ic3_after=pr["result"], ic3_invariant=pr.get("invariant"), ic3_seconds=round(time.time() - t0, 2))
        if have_kind2:
            lp = os.path.join(a.out, f"m{i:03d}.lus"); lustre.emit(Sn, lp)
            kr, dt, _ = lustre.check(lp)
            row.update(kind2_before=kbase.get(k), kind2_after=kr.get(k), kind2_seconds=round(dt, 2))
        rows.append(row)
        print(f"{mu['id']:28s} {mu['change']:40s} eq={eq!s:5s} diff={nd:3d}/{tot:<4d} {order:12s} "
              f"+conf={len(row['conflicts_added'])} -conf={len(row['conflicts_removed'])} dholes={row['holes_delta']:+d} "
              f"ic3={row['ic3_before']}->{row['ic3_after']} kind2={row.get('kind2_before')}->{row.get('kind2_after')}")
        os.remove(path)
    PRES = ("reorder", "demorgan", "dneg")
    pres = [r for r in rows if r["op"] in PRES]
    rows_all, rows = rows, [r for r in rows if r["op"] not in PRES]
    nonEq = [r for r in rows if not r["miter_equivalent"]]
    sat_before = [r for r in nonEq if r["ic3_before"] == "proved"]
    summ = dict(model=os.path.relpath(a.model, ROOT), mutants=len(rows),
                by_operator={op: sum(r["op"] == op for r in rows) for op in ("drop", "negate", "retarget")},
                meaning_preserving=dict(mutants=len(pres), by_operator={op: sum(r["op"] == op for r in pres) for op in PRES},
                                        miter_equivalent=sum(r["miter_equivalent"] for r in pres),
                                        ic3_verdict_changed=sum(r["ic3_before"] != r["ic3_after"] for r in pres),
                                        circuit_conflict_or_hole_change=sum(bool(r["conflicts_added"] or r["conflicts_removed"] or r["holes_delta"]) for r in pres)),
                mutants_of_requirements_the_design_satisfies=len(sat_before),
                of_those_verdict_unchanged=sum(r["ic3_before"] == r["ic3_after"] for r in sat_before),
                mutants_of_requirements_the_design_violates=len(nonEq) - len(sat_before),
                of_those_verdict_unchanged_=sum(r["ic3_before"] == r["ic3_after"] for r in nonEq if r not in sat_before),
                equivalent_mutants=len(rows) - len(nonEq),
                miter_detected=len(nonEq), miter_localized_to_requirement=len(nonEq),
                circuit_conflict_or_hole_change=sum(bool(r["conflicts_added"] or r["conflicts_removed"] or r["holes_delta"]) for r in nonEq),
                design_verdict_changed_circuit=sum(r["design_violates_before"] != r["design_violates_after"] for r in nonEq))
    summ["ic3_verdict_changed"] = sum(r["ic3_before"] != r["ic3_after"] for r in nonEq)
    summ["one_step_violation_unreachable"] = sum(r["design_violates_after"] and r["ic3_after"] == "proved" for r in rows)
    if have_kind2:
        summ["kind2_agrees_with_ic3"] = f"{sum((r['kind2_after'] == 'valid') == (r['ic3_after'] == 'proved') for r in rows_all)}/{len(rows_all)}"
        summ["kind2_verdict_changed"] = sum(r["kind2_before"] != r["kind2_after"] for r in nonEq)
        summ["kind2_agrees_with_circuit_design_check"] = sum((r["kind2_after"] == "invalid") == r["design_violates_after"] for r in rows)
    summ["detected_by_any_circuit_check"] = sum(bool(r["conflicts_added"] or r["conflicts_removed"] or r["holes_delta"]
                                                     or r["design_violates_before"] != r["design_violates_after"]) for r in nonEq)
    json.dump(dict(summary=summ, mutants=rows_all), open(os.path.join(a.out, "mutation.json"), "w"), indent=1, ensure_ascii=False)
    print(json.dumps(summ, indent=1))


if __name__ == "__main__":
    main()
