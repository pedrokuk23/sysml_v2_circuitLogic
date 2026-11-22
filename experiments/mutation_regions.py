#!/usr/bin/env python3
"""Full-region comparison for the defect-injection experiment (complements experiments/mutation.py).

mutation.py records a summary of the circuit checks for each mutant: the identities of the conflicting pairs and the
total number of hole situations. A mutant can move a conflict or a hole region without changing that summary. This
script compares the complete regions instead, on the finite domain of each state machine (current state x valuations
of the Boolean inputs read by the machine's requirements, original and mutated):

  conflict region of a pair (i, j)  the situations in which both antecedents hold and the demanded next states differ;
  hole region                       the situations in which no antecedent holds.

A mutant changes the regions when the set of (pair, situation) and (hole, situation) elements differs from the
original's. The mutants are regenerated with mutation.mutants() (same identifiers as in mutation.json), and the
result is merged into the given mutation.json as the field 'regions_changed' of each mutant and a summary block
'full_region_comparison'; the IC3 and Kind 2 fields are not recomputed.

    python3 experiments/mutation_regions.py [--model MODEL] [--json results/reference/mutation/mutation.json]
"""
import argparse, itertools, json, os, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
sys.path.insert(0, HERE)
from z3 import BoolVal, IntVal, substitute, simplify, is_true, is_false  # noqa: E402
from semantics import compile_model  # noqa: E402
import analysis  # noqa: E402
import mutation  # noqa: E402


def universe(S):
    """Per machine: Boolean inputs read by the machine's transition requirements."""
    return {m: {str(b) for f in g["reqs"].values() for b in analysis.bools_in(f, S)}
            for m, g in analysis.machine_groups(S).items()}


def regions(S, univ):
    out = set()
    for m, g in analysis.machine_groups(S).items():
        ins = sorted(univ[m])
        lits = S.enums[g["enum"]]
        for i in range(len(lits)):
            for bits in itertools.product((False, True), repeat=len(ins)):
                sub = [(g["cur"], IntVal(i))] + [(S.vars[n], BoolVal(b)) for n, b in zip(ins, bits) if n in S.vars]
                on = {}
                for k, f in g["reqs"].items():
                    a = simplify(substitute(f.arg(0), *sub))
                    if not (is_true(a) or is_false(a)):
                        raise ValueError(f"{k}: antecedent not decided by state and inputs: {a}")
                    if is_true(a):
                        on[k] = analysis.target(f)
                sit = (m, lits[i], bits)
                if not on:
                    out.add(("hole",) + sit)
                for (k1, t1), (k2, t2) in itertools.combinations(sorted(on.items()), 2):
                    if t1 != t2:
                        out.add(("conflict", k1, k2) + sit)
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--model", default=mutation.MODEL)
    ap.add_argument("--json", default=os.path.join(ROOT, "results", "reference", "mutation", "mutation.json"))
    a = ap.parse_args()
    text = open(a.model).read()
    So = compile_model(a.model)
    MS = mutation.mutants(text, So.enums)
    data = json.load(open(a.json))
    rows = {r["id"]: r for r in data["mutants"]}
    assert set(rows) == {m["id"] for m in MS}, "mutants differ from those of mutation.json"
    comp = {}
    for mu in MS:
        f = tempfile.NamedTemporaryFile("w", suffix=".sysml", delete=False); f.write(mu["text"]); f.close()
        Sn = compile_model(f.name); os.unlink(f.name)
        U = {m: universe(So)[m] | universe(Sn)[m] for m in So.ir["machines"]}
        ro, rn = regions(So, U), regions(Sn, U)
        comp[mu["id"]] = ro != rn
        r = rows[mu["id"]]
        r["regions_changed"] = ro != rn
        r["region_elements_added"] = len(rn - ro)
        r["region_elements_removed"] = len(ro - rn)
    PRES = ("reorder", "demorgan", "dneg")
    summ_rows = lambda f: [r for r in data["mutants"] if f(r)]
    nonEq = summ_rows(lambda r: r["op"] not in PRES and not r["miter_equivalent"])
    pres = summ_rows(lambda r: r["op"] in PRES)
    sat_b = [r for r in nonEq if r["ic3_before"] == "proved"]
    vio_b = [r for r in nonEq if r["ic3_before"] != "proved"]
    summary_change = lambda r: bool(r["conflicts_added"] or r["conflicts_removed"] or r["holes_delta"])
    data["full_region_comparison"] = dict(
        meaning_changing=len(nonEq), regions_changed=sum(r["regions_changed"] for r in nonEq),
        of_requirements_satisfied=f"{sum(r['regions_changed'] for r in sat_b)}/{len(sat_b)}",
        of_requirements_violated=f"{sum(r['regions_changed'] for r in vio_b)}/{len(vio_b)}",
        meaning_preserving=len(pres), meaning_preserving_regions_changed=sum(r["regions_changed"] for r in pres),
        summary_changed=sum(summary_change(r) for r in nonEq),
        regions_changed_but_summary_unchanged=sum(r["regions_changed"] and not summary_change(r) for r in nonEq),
        summary_changed_but_regions_unchanged=sum(summary_change(r) and not r["regions_changed"] for r in nonEq),
        example_moved_region=next((dict(id=r["id"], change=r["change"], added=r["region_elements_added"],
                                        removed=r["region_elements_removed"])
                                   for r in nonEq if r["regions_changed"] and not summary_change(r)), None))
    json.dump(data, open(a.json, "w"), indent=1, ensure_ascii=False)
    print(json.dumps(data["full_region_comparison"], indent=1))


if __name__ == "__main__":
    main()
