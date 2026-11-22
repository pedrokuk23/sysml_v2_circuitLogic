#!/usr/bin/env python3
"""Independent cross-check of the reachability analysis (analysis.reachable_situations, BFS with z3) by Kind 2.
The composed design is emitted as a Lustre node (lustre.emit); for every composite state s of the machines a property
'not (state = s)' is added. Kind 2 proves it valid iff s is unreachable from the initial states, and returns a trace
reaching s otherwise. The verdicts must coincide with the set computed by the compiler.

    python3 experiments/kind2_reachability.py [OUTDIR]     (default results/reference/kind2_reach)
"""
import itertools, json, os, re, sys, time
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from semantics import compile_model
import analysis, lustre


def main(model, outdir):
    os.makedirs(outdir, exist_ok=True)
    S = compile_model(model)
    res = analysis.check_machines(S)
    reach = analysis.reachable_situations(S, res)
    machines = list(S.ir["machines"])
    mv = {m: S.machine_vars(m) for m in machines}
    lits = {m: S.enums[mv[m][0]] for m in machines}
    path = os.path.join(outdir, "reach.lus")
    lustre.emit(S, path)
    text = open(path).read()
    props, names = [], {}
    for combo in itertools.product(*[range(len(lits[m])) for m in machines]):
        tag = "reach_" + "_".join(lits[m][v] for m, v in zip(machines, combo))
        cond = " and ".join(f"v_{mv[m][1]} = {v}" for m, v in zip(machines, combo))
        props.append(f"  --%PROPERTY \"{tag}\" not ({cond});")
        names[tag] = {m: lits[m][v] for m, v in zip(machines, combo)}
    # keep only the reachability properties
    text = re.sub(r"  --%PROPERTY .*\n", "", text)
    text = text.replace("tel\n", "\n".join(props) + "\ntel\n")
    open(path, "w").write(text)
    verdicts, dt, log = lustre.check(path)
    open(os.path.join(outdir, "kind2.log"), "w").write(log)
    kind2_reach = sorted([names[t] for t, v in verdicts.items() if v == "invalid"], key=str)
    kind2_unreach = sorted([names[t] for t, v in verdicts.items() if v == "valid"], key=str)
    unknown = [t for t in names if verdicts.get(t) not in ("valid", "invalid")]
    agree = kind2_reach == reach["states"] and not unknown
    out = dict(model=os.path.basename(model), composite_states=len(names), reachable_compiler=reach["states"],
               reachable_kind2=kind2_reach, unreachable_kind2=kind2_unreach, unknown=unknown, agree=agree,
               seconds=round(dt, 2))
    json.dump(out, open(os.path.join(outdir, "kind2_reachability.json"), "w"), indent=1)
    print(f"{out['model']}: compiler {reach['n_states']}/{len(names)} reachable, Kind 2 {len(kind2_reach)} reachable, "
          f"{len(kind2_unreach)} proved unreachable, {len(unknown)} unknown; agree={agree} ({dt:.1f} s)")
    return agree


if __name__ == "__main__":
    ok = True
    outs = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "results", "reference", "kind2_reach")
    for m in [os.path.join(ROOT, "models", f) for f in ("lmcps_fsm.sysml", "lmcps_fsm_rev.sysml")]:
        ok &= main(m, os.path.join(outs, os.path.basename(m)[:-6]))
    sys.exit(0 if ok else 1)
