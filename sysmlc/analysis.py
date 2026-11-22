"""Logic checks on the IR (z3). Each check runs only if the model has the elements it needs."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import (And, Or, Not, Implies, Exists, ForAll, BoolVal, RealVal, Real, If, simplify, substitute, is_true,
                is_implies, is_eq, is_int_value)
from logic_engine import conflicts, is_sat, valid, qe, finite_region, coverage, free_consts, refines, abduce, interpolate, has_quantifier, dead_parts


def bools_in(f, S):
    names = set(free_consts(f))
    return [v for n, v in S.vars.items() if n in names and S.vtype.get(n) == "Boolean"]


def target(f):
    a, b = f.arg(1).arg(0), f.arg(1).arg(1)
    return (b if is_int_value(b) else a).as_long()


# formulas are reported in results.json as text: never let the Z3 printer elide a long one with '...'
from z3 import set_option as _set_option
_set_option(max_args=10 ** 7, max_lines=10 ** 7, max_depth=10 ** 7, max_visited=10 ** 7)

def is_glossary(rid):
    return rid.startswith("GLO")


# ------------------------------------------------------------------ state machines and their requirements
def machine_groups(S):
    """For each machine: the requirements of the form  antecedent -> next == literal."""
    out = {}
    for mname in S.ir["machines"]:
        enum, cur, nxt = S.machine_vars(mname)
        g = {}
        for k, f in S.R.items():
            if is_implies(f) and is_eq(f.arg(1)):
                a, b = f.arg(1).arg(0), f.arg(1).arg(1)
                if (a.eq(nxt) and is_int_value(b)) or (b.eq(nxt) and is_int_value(a)):
                    g[k] = f
        out[mname] = dict(enum=enum, cur=cur, nxt=nxt, reqs=g)
    return out


def check_machines(S):
    res = {}
    groups = machine_groups(S)
    dom_cur = And(*[And(g["cur"] >= 0, g["cur"] < len(S.enums[g["enum"]])) for g in groups.values()])
    all_next = [g["nxt"] for g in groups.values()]
    for mname, g in groups.items():
        lits = S.enums[g["enum"]]
        ins = sorted({b for f in g["reqs"].values() for b in bools_in(f, S)}, key=str)
        en = {g["cur"]: dict(enumerate(lits))}
        # conflicts = bus contention
        C = conflicts(g["reqs"], S.domain, [g["cur"]] + ins, max_size=2)
        for c in C:
            fs = [g["reqs"][k] for k in c["requirements"]]
            c["region"] = finite_region(And(dom_cur, Not(Exists(all_next, And(S.domain, *fs)))), bools_in(And(*fs), S), en)
        # repairs by priority (antecedent of the loser gets the negated antecedent of the winner)
        for c in C:
            if len(c["requirements"]) == 1:     # a single requirement against A: no priority repair applies
                c["repairs"] = {}
                continue
            a, b = c["requirements"]
            c["repairs"] = {f"{x} yields to {y}": str(Implies(And(g["reqs"][x].arg(0), Not(g["reqs"][y].arg(0))), g["reqs"][x].arg(1)))
                            for x, y in ((a, b), (b, a))}
        # holes = floating outputs
        holes = {}
        for i, lab in enumerate(lits):
            antes = [f.arg(0) for f in g["reqs"].values() if is_sat(f.arg(0), g["cur"] == i)[0]]
            hole = And(g["cur"] == i, Not(Or(*antes))) if antes else (g["cur"] == i)
            n = sum(1 for bits in itertools.product([0, 1], repeat=len(ins))
                    if is_sat(hole, *[b if x else Not(b) for b, x in zip(ins, bits)])[0])
            holes[lab] = dict(n=n, of=2 ** len(ins), region=finite_region(hole, ins, {}))
        # design (the state machine itself) against each requirement of the group
        rel = S.machine_relation(mname)
        viol = {}
        for k, f in g["reqs"].items():
            ok, _ = valid(f, And(S.domain, rel))
            if not ok:
                viol[k] = finite_region(And(S.domain, rel, Not(f)), ins, en)
        # transitions of one state with overlapping guards: only there does the textual priority matter
        M = S.ir["machines"][mname]
        overlap = [[a["id"], b["id"]] for a, b in itertools.combinations(M["transitions"], 2)
                   if a["src"] == b["src"] and is_sat(And(S.domain, S.E(a["guard"]), S.E(b["guard"])))[0]]
        res[mname] = dict(enum=g["enum"], cur=str(g["cur"]), next=str(g["nxt"]), inputs=[str(b) for b in ins],
                          overlapping_guards=overlap,
                          requirements=list(g["reqs"]), contention=C, holes=holes, design_violates=viol)
    return res


def check_port_contracts(S, machines):
    out = {}
    for name, expr in S.ir["asserts"].items():
        a = S.E(expr)
        sig = {str(b) for b in bools_in(a, S)}
        defs = [S.R[k] for k, r in S.ir["requirements"].items()
                if any(x["dir"] == "out" and x["name"] in sig for x in r["attrs"])]
        if not defs:
            continue
        body = And(S.domain, *defs)
        loc = [v for n, v in free_consts(body).items() if n not in sig]
        proj = qe(Exists(loc, body))
        res = dict(asserted=expr, projection=str(proj), equivalent=valid(proj == a)[0], strongest=valid(Implies(proj, a))[0])
        # effect on the machines that read these signals: their holes under the contract
        for mname, m in machines.items():
            if not sig & set(m["inputs"]):
                continue
            enum, cur, nxt = S.machine_vars(mname)
            g = machine_groups(S)[mname]
            ins = [S.vars[n] for n in m["inputs"]]
            tot = {}
            for tag, ctx in (("without_contract", BoolVal(True)), ("with_contract", a)):
                n = 0
                for i in range(len(S.enums[enum])):
                    antes = [f.arg(0) for f in g["reqs"].values() if is_sat(f.arg(0), cur == i)[0]]
                    hole = And(cur == i, ctx, Not(Or(*antes)) if antes else BoolVal(True))
                    n += sum(1 for bits in itertools.product([0, 1], repeat=len(ins))
                             if is_sat(hole, *[b if x else Not(b) for b, x in zip(ins, bits)])[0])
                tot[tag] = n
            res[f"holes_{mname}"] = tot
        out[name] = res
    return out


# ------------------------------------------------------------------ variability and allocation
def check_variability(S):
    if not S.usages:
        return None
    ir = S.ir
    names = {u: [v for v, _ in ir["variations"][d]] for u, d in S.usages.items()}
    U = list(S.usages)
    R = {k: f for k, f in S.R.items()}
    acts = {n: a for ad in ir["actions"].values() for n, a in ad["attrs"].items()}
    funs = [n for n, a in acts.items() if "cpuLoad" in a]
    for f in funs:
        S.onboard.setdefault(f, __import__("z3").Bool(f"onboard_{f}"))
    fixed = [f for f in funs if acts[f].get("fixedOnBoard")]
    cap_u = next((u for u in U if all("cpuCapacity" in a for _, a in ir["variations"][S.usages[u]])), None)
    if funs and cap_u:
        R["CAP"] = sum(If(S.onboard[f], RealVal(acts[f]["cpuLoad"]), RealVal(0)) for f in funs) <= S.variant_attr(cap_u, "cpuCapacity")
    dom = And(S.domain, *[S.onboard[f] for f in fixed])
    configs = list(itertools.product(*[range(len(names[u])) for u in U]))
    label = lambda c: {u: names[u][k] for u, k in zip(U, c)}
    valid_c, cores = [], {}
    for c in configs:
        pick = And(*[S.sel[u] == k for u, k in zip(U, c)])
        if is_sat(dom, pick, *R.values())[0]:
            valid_c.append(c)
        else:
            core = list(R)
            for k in list(core):
                if not is_sat(dom, pick, *[R[j] for j in core if j != k])[0]:
                    core.remove(k)
            cores[" + ".join(core)] = cores.get(" + ".join(core), 0) + 1
    # for each requirement: how many configurations it eliminates ON ITS OWN (independent of deletion order)
    alone = {}
    for c in configs:
        if c in valid_c:
            continue
        pick = And(*[S.sel[u] == k for u, k in zip(U, c)])
        for k in R:
            if not is_sat(dom, pick, R[k])[0]:
                alone[k] = alone.get(k, 0) + 1
    dead, core_v, why = [], [], {}
    if not valid_c:                                    # dead/core are meaningless without a valid configuration
        return dict(variations=names, n_configs=len(configs), n_valid=0, inconsistent=True,
                    invalid_by_core=cores, eliminated_alone=alone, dead_variants=[], core_variants=[],
                    dead_because={}, revive={}, allocation=[], allocation_functions=funs)
    for u in U:
        for k, n in enumerate(names[u]):
            used = [c for c in valid_c if c[U.index(u)] == k]
            if not used:
                dead.append(f"{u}.{n}")
                core = list(R)
                for j in list(core):
                    if not is_sat(dom, S.sel[u] == k, *[R[i] for i in core if i != j])[0]:
                        core.remove(j)
                why[f"{u}.{n}"] = core
            elif len(used) == len(valid_c):
                core_v.append(f"{u}.{n}")
    # abduction for each dead variant: free the attributes of the other usages read by the killing requirement
    revive = {}
    for dv, core in why.items():
        u, n = dv.split("."); k = names[u].index(n)
        for rid in core:
            if rid not in S.ir["requirements"]:
                continue
            free = {}
            def res2(name, _u=u):
                ps = name.split(".")
                for i_, seg in enumerate(ps[:-1]):
                    if seg in S.usages and seg != _u:
                        key = f"{seg}.{ps[i_ + 1]}"
                        return free.setdefault(key, Real(key))
                return S.resolve(name)
            from semantics import Expr
            f = Expr(res2, S.enums)(S.ir["requirements"][rid]["expr"])
            f = substitute(f, (S.sel[u], __import__("z3").IntVal(k)))
            W = simplify(f)
            pos = [v > 0 for v in free.values()]
            revive[f"{dv} / {rid}"] = dict(free=list(free), condition=str(qe(W) if free else W),
                                           possible=is_sat(W, *pos)[0])
    alloc = []
    if funs:
        for c in valid_c:
            pick = And(*[S.sel[u] == k for u, k in zip(U, c)])
            feas = []
            for bits in itertools.product([False, True], repeat=len(funs)):
                if is_sat(dom, pick, *[S.onboard[f] == b for f, b in zip(funs, bits)], *R.values())[0]:
                    feas.append(dict(zip(funs, bits)))
            forced = {f: ("OBC" if feas[0][f] else "ground") for f in funs if f not in fixed and all(x[f] == feas[0][f] for x in feas)}
            decl = {f: any(fn == f for fn, _ in ir["allocations"]) for f in funs}
            alloc.append(dict(config=label(c), feasible_allocations=len(feas), forced=forced,
                              fixed=fixed, declared_feasible=decl in feas))
    return dict(variations=names, n_configs=len(configs), n_valid=len(valid_c), valid_configs=[label(c) for c in valid_c],
                invalid_by_core=cores, eliminated_alone=alone, dead_variants=dead, core_variants=core_v, dead_because=why, revive=revive,
                allocation=alloc, allocation_functions=funs)


# ------------------------------------------------------------------ action flows
def check_actions(S):
    out = {}
    for aname, A in S.ir["actions"].items():
        kind, edges = A["kind"], A["edges"]
        if not edges:
            continue
        inputs = {n: S.vars[n] for n in A["inputs"]}
        dec = {}
        for n, k in kind.items():
            if k == "decide":
                cases = {d: S.E(gd) for (s, d, gd) in edges if s == n}
                cv = coverage(cases)
                dec[n] = dict(guards={d: gd for (s, d, gd) in edges if s == n}, complete=cv["complete"],
                              hole=cv.get("hole_region"), overlaps=[o["cases"] for o in cv["overlaps"]])
        inc = {n: [i for i, e in enumerate(edges) if e[1] == n] for n in kind}
        outg = {n: [i for i, e in enumerate(edges) if e[0] == n] for n in kind}
        flows = []
        for bits in itertools.product([False, True], repeat=len(inputs)):
            val = dict(zip(inputs, bits))
            sub = [(inputs[k], BoolVal(v)) for k, v in val.items()]
            m0 = tuple(1 if i in outg[next(n for n, k in kind.items() if k == "start")] else 0 for i in range(len(edges)))
            seen, todo, graph, term = {m0}, [m0], {}, {}
            while todo:
                m = todo.pop()
                en = []
                for n, k in kind.items():
                    if k == "start":
                        continue
                    have = [i for i in inc[n] if m[i] > 0]
                    if k == "join":
                        if have and len(have) == len(inc[n]):
                            en.append((tuple(inc[n]), tuple(outg[n])))
                        continue
                    for i in have:
                        if k == "decide":
                            for o in outg[n]:
                                if is_true(simplify(substitute(S.E(edges[o][2]), *sub))):
                                    en.append(((i,), (o,)))
                        else:
                            en.append(((i,), tuple(outg[n])))
                graph[m] = []
                if not en:
                    term[m] = [f"{edges[i][0]}→{edges[i][1]}" for i in range(len(edges)) if m[i] > 0]
                    continue
                for cons, prod in en:
                    mm = list(m)
                    for i in cons: mm[i] -= 1
                    for i in prod: mm[i] += 1
                    mm = tuple(min(x, 3) for x in mm)
                    graph[m].append(mm)
                    if mm not in seen:
                        seen.add(mm); todo.append(mm)
            color, cyc = {}, [False]
            def dfs(x):
                color[x] = 1
                for y in graph.get(x, []):
                    if color.get(y) == 1: cyc[0] = True
                    elif y not in color: dfs(y)
                color[x] = 2
            dfs(m0)
            flows.append(dict(inputs=val, markings=len(seen), terminates=any(not v for v in term.values()),
                              deadlocks=[v for v in term.values() if v], loop_possible=cyc[0]))
        dur = {n: A["attrs"].get(n, {}).get("duration", 0.0) for n in kind}
        # nominal cycle time: longest path from start to the final node that visits no node twice. A path that is
        # cut by a cycle does not reach the final node and is not counted.
        # Parallel fork branches are approximated by the longest branch (max over branches).
        NEG = float("-inf")
        def longest(n, stack=()):
            if kind[n] == "final":
                return 0.0
            best = NEG
            for i in outg[n]:
                t = edges[i][1]
                if t in stack or t == n:
                    continue
                best = max(best, longest(t, stack + (n,)))
            return dur.get(n, 0.0) + best if best != NEG else NEG
        start = next(n for n, k in kind.items() if k == "start")
        out[aname] = dict(nodes=kind, edges=[list(e) for e in edges], decisions=dec, flows=flows,
                          nominal_cycle_min=longest(start),
                          loops=cycle_durations(kind, edges, outg, dur))
    return out


def cycle_durations(kind, edges, outg, dur):
    """For every node on a cycle: the minimal total duration of a cycle through it (time added per loop)."""
    import heapq
    out = {}
    for n in kind:
        best, pq, seen = None, [(0.0, edges[i][1]) for i in outg[n]], set()
        heapq.heapify(pq)
        while pq:
            d, x = heapq.heappop(pq)
            if x == n:
                best = d + dur.get(n, 0.0); break
            if x in seen:
                continue
            seen.add(x)
            for i in outg.get(x, []):
                heapq.heappush(pq, (d + dur.get(x, 0.0), edges[i][1]))
        if best is not None:
            out[n] = best
    return out


# ------------------------------------------------------------------ parents (satisfy) in one step
def check_parents_one_step(S):
    machines = list(S.ir["machines"])
    if not machines:
        return None
    rels = [S.machine_relation(m) for m in machines]
    gl = [f for k, f in S.R.items() if is_glossary(k)]
    groups = machine_groups(S)
    inner = {k for g in groups.values() for k in g["reqs"]}
    res = {}
    for k, f in S.R.items():
        if k in inner or is_glossary(k) or any(n.startswith("pre") for n in free_consts(f)):
            continue
        ok, m = valid(f, And(S.domain, *rels, *gl))
        res[k] = dict(valid=ok, counterexample={str(d): str(m[d]) for d in m.decls()} if m else None)
    return res


def check_divisions(S):
    """Hypothesis of the faithful-translation proposition: every denominator is nonzero under the assumptions A
    (domain and glossary axioms). Returns the divisions whose denominator A does not keep away from zero."""
    from z3 import is_app_of, Z3_OP_DIV
    A = And(S.domain, *[f for k, f in S.R.items() if is_glossary(k)])
    bad, n = [], 0
    seen = set()

    def walk(e, k):
        nonlocal n
        if is_app_of(e, Z3_OP_DIV) and (k, str(e.arg(1))) not in seen:
            seen.add((k, str(e.arg(1)))); n += 1
            if not valid(e.arg(1) != 0, A)[0]:
                bad.append(dict(requirement=k, denominator=str(e.arg(1))))
        for c in e.children():
            walk(c, k)
    for k, f in S.R.items():
        walk(f, k)
    return dict(divisions=n, denominator_may_be_zero=bad)


def run_all(S):
    out = dict(model=S.ir["source"], requirements=list(S.ir["requirements"]))
    out["division_hypothesis"] = check_divisions(S)
    if S.ir["machines"]:
        out["machines"] = check_machines(S)
        out["reachability"] = reachable_situations(S, out["machines"])
        out["port_contracts"] = check_port_contracts(S, out["machines"])
        out["parents_one_step"] = check_parents_one_step(S)
    og = check_output_groups(S)
    if og:
        out["output_groups"] = og
    fd = check_flowdown(S)
    if fd:
        out["flowdown"] = fd
    v = check_variability(S)
    if v:
        out["variability"] = v
    a = check_actions(S)
    if a:
        out["actions"] = a
    return out


# ------------------------------------------------------------------ reachability of the composed machines
def reachable_situations(S, res):
    """Restrict the one-step results (conflicts, holes, design violations) to the situations that the composed
    state machines can reach from their initial states. A situation is a current state of the machine together
    with a valuation of its input signals; the state of the other machines and the free inputs are existentially
    quantified, and signals defined by glossary axioms follow from them. Adds 'reachable' entries to res."""
    from z3 import Solver, sat
    machines = list(S.ir["machines"])
    if not machines:
        return None
    vars_ = {m: S.machine_vars(m) for m in machines}
    lits = {m: S.enums[vars_[m][0]] for m in machines}
    glossary = [f for k, f in S.R.items() if is_glossary(k)]
    Z = And(S.domain, *[S.machine_relation(m) for m in machines], *glossary)
    init = tuple(lits[m].index(S.ir["machines"][m]["init"]) for m in machines)
    seen, frontier = {init}, [init]
    while frontier:
        st = frontier.pop()
        s = Solver(); s.add(Z, *[vars_[m][1] == v for m, v in zip(machines, st)])
        while s.check() == sat:
            mdl = s.model()
            nx = tuple(mdl.eval(vars_[m][2], model_completion=True).as_long() for m in machines)
            if nx not in seen:
                seen.add(nx); frontier.append(nx)
            s.add(Or(*[vars_[m][2] != v for m, v in zip(machines, nx)]))
    reach = Or(*[And(*[vars_[m][1] == v for m, v in zip(machines, st)]) for st in seen])
    # the composition is a function on the reachable states: for every input, exactly one tuple of next states
    from z3 import substitute as _sub, ForAll as _forall, Const as _const
    outs = [S.vars[a["name"]] for r in S.ir["requirements"].values() for a in r["attrs"]
            if a["dir"] == "out" and a["name"] in S.vars]
    outs = list({str(v): v for v in outs}.values())
    ren = [(v, _const(str(v) + "__2", v.sort())) for v in outs]
    Z2 = _sub(Z, *ren)
    s = Solver(); s.add(Z, Z2, reach, Or(*[vars_[m][2] != _sub(vars_[m][2], *ren) for m in machines]))
    unique = s.check() != sat
    s = Solver(); s.add(S.domain, reach, _forall(outs, Not(Z)) if outs else Not(Z))
    total = s.check() != sat
    out = dict(composition_deterministic=unique, composition_total=total, states=sorted([{m: lits[m][v] for m, v in zip(machines, st)} for st in seen], key=str),
               n_states=len(seen), n_states_total=1)
    for m in machines:
        out["n_states_total"] *= len(lits[m])
    for m, r in res.items():
        enum, cur, nxt = vars_[m]
        ins = [S.vars[n] for n in r["inputs"]]

        def count(cond):
            n = 0
            for i in range(len(lits[m])):
                for bits in itertools.product([False, True], repeat=len(ins)):
                    if is_sat(And(Z, reach, cur == i, cond, *[b if x else Not(b) for b, x in zip(ins, bits)]))[0]:
                        n += 1
            return n
        g = machine_groups(S)[m]
        for c in r["contention"]:
            a, b = c["requirements"]
            both = And(g["reqs"][a].arg(0), g["reqs"][b].arg(0))
            c["situations_one_step"] = sum(1 for i in range(len(lits[m])) for bits in itertools.product([False, True], repeat=len(ins))
                                           if is_sat(And(S.domain, cur == i, both, *[x if y else Not(x) for x, y in zip(ins, bits)]))[0])
            c["situations_reachable"] = count(both)
        antes = Or(*[f.arg(0) for f in g["reqs"].values()]) if g["reqs"] else BoolVal(False)
        r["holes_reachable"] = {lab: sum(1 for bits in itertools.product([False, True], repeat=len(ins))
                                         if is_sat(And(Z, reach, cur == i, Not(antes), *[b if x else Not(b) for b, x in zip(ins, bits)]))[0])
                                for i, lab in enumerate(lits[m])}
        r["situations_reachable"] = count(BoolVal(True))
        r["situations_total"] = len(lits[m]) * 2 ** len(ins)
        r["design_violates_reachable"] = [k for k in r["design_violates"]
                                          if is_sat(And(Z, reach, Not(g["reqs"][k])))[0]]
    return out


# ------------------------------------------------------------------ quantitative flow-down along refinements
def _atoms(f, out):
    from z3 import is_app, is_and, is_or, is_not, is_implies as _imp
    if is_and(f) or is_or(f) or is_not(f) or _imp(f):
        for c in f.children():
            _atoms(c, out)
    elif f.sort().name() == "Bool" and f.num_args() == 2:
        if not any(f.eq(o) for o in out):
            out.append(f)
    return out


def _unsat(*fs):
    from z3 import Solver, unsat
    s = Solver(); s.add(*fs)
    return s.check() == unsat


def _sup(expr, hyp, lo=-1e12, hi=1e12, iters=200, rel=1e-9):
    """Supremum of a real expression under hyp (bisection with SMT); None if unbounded or infeasible. An 'unknown'
    answer counts as satisfiable, so that the bound returned is never below the supremum."""
    from z3 import Solver, unsat

    def possible(*fs):
        s = Solver(); s.add(hyp, *fs)
        return s.check() != unsat
    if not is_sat(hyp)[0] or possible(expr > hi):
        return None
    for _ in range(iters):
        mid = (lo + hi) / 2
        if possible(expr > mid):
            lo = mid
        else:
            hi = mid
        if hi - lo <= rel * max(1.0, abs(hi)):
            break
    return hi


def _abduce_bounded(P, rest, A, voc, ms=20000):
    """Abduction with a time limit on quantifier elimination. Nonlinear real arithmetic can make QE very slow;
    when it does not finish and the vocabulary is a single quantity v, the weakest replacement is computed
    numerically as the set of values of v for which  A & rest -> P  is valid (bisection between valid and
    invalid points of a logarithmic grid); the result is then marked 'numerical'."""
    from z3 import Tactic, TryFor, ForAll, substitute, RealVal, simplify as _simp
    body = Implies(And(A, *rest), P)
    names = {str(v) for v in voc}
    others = [v for n, v in free_consts(body).items() if n not in names]
    W = None
    for t in ("qe2", "qe"):
        try:
            W = _simp(Tactic("ctx-solver-simplify")(TryFor(Tactic(t), ms)(ForAll(others, body) if others else body).as_expr()).as_expr())
            if has_quantifier(W):          # elimination did not complete
                W = None
                continue
            break
        except Exception:
            continue
    if W is not None:
        return dict(W=str(W), W_expr=W, method="quantifier elimination")
    if len(voc) != 1:
        return dict(W=None, W_expr=None, method=f"not computed (quantifier elimination exceeded {ms // 1000} s)")
    v = voc[0]
    ok = lambda c: valid(substitute(body, (v, RealVal(c))))[0]
    grid = sorted({sg * 10 ** (e / 4) for sg in (-1, 1) for e in range(-40, 41)} | {0.0})
    flags = [ok(c) for c in grid]
    if not any(flags):
        return dict(W="False", W_expr=BoolVal(False), method="numerical (no value of the grid)")
    bounds = []
    for (a, fa), (b, fb) in zip(zip(grid, flags), zip(grid[1:], flags[1:])):
        if fa != fb:
            lo, hi = a, b
            for _ in range(80):
                mid = (lo + hi) / 2
                if ok(mid) == fa:
                    lo = mid
                else:
                    hi = mid
            # report each bound rounded to six significant digits towards the valid side
            x = lo if (fa and a < b) else hi
            r = float(f"{x:.6g}")
            ok_r = ok(r)
            k = 0
            while not ok_r and k < 20:          # move the rounded bound into the valid side
                x = x - abs(x) * 1e-6 if (fa and a < b) else x + abs(x) * 1e-6
                r = float(f"{x:.6g}"); ok_r = ok(r); k += 1
            bounds.append((("<=" if fa else ">="), r))
    expr = And(*[(v <= c) if op == "<=" else (v >= c) for op, c in bounds]) if bounds else BoolVal(True)
    return dict(W=" and ".join(f"{v} {op} {c:g}" for op, c in bounds) or "True", W_expr=expr,
                method="numerical (bisection; quantifier elimination exceeded the time limit)")


def _interpolate_bounded(fa, fb, shared, ms=20000):
    """Strongest (exists local_a. fa) and weakest (forall local_b. not fb) interpolants, with a time limit on QE."""
    from z3 import Tactic, TryFor, Exists, ForAll, simplify as _simp
    names = {str(v) for v in shared}
    la = [v for n, v in free_consts(fa).items() if n not in names]
    lb = [v for n, v in free_consts(fb).items() if n not in names]

    def q(f):
        for t in ("qe2", "qe"):
            try:
                r = _simp(Tactic("ctx-solver-simplify")(TryFor(Tactic(t), ms)(f).as_expr()).as_expr())
                if not has_quantifier(r):
                    return r
            except Exception:
                continue
        return None
    st = q(Exists(la, fa)) if la else fa
    wk = q(ForAll(lb, Not(fb))) if lb else _simp(Not(fb))
    return dict(strongest=str(st) if st is not None else None, weakest=str(wk) if wk is not None else None,
                strongest_expr=st, weakest_expr=wk)


def input_total(body, A, outputs):
    """For every input valuation admitted by A (projected on the inputs), some output valuation satisfies body:
    validity of  (exists outputs. A) -> (exists outputs. body)."""
    from z3 import Exists as _Ex
    return valid(Implies(_Ex(outputs, A), _Ex(outputs, body)))[0]


def check_flowdown(S):
    """For each #refinement dependency (target <- sources): refinement as a tautology, worst case of the
    parent's bounded quantity, abduction by replacement of one or two children (vocabulary: the quantities of the
    replaced children), interface contracts between the subsystems of the children (strongest and weakest Craig
    interpolants over the shared quantity, and the margin between them), and the discretisation of the refinement
    into Boolean lemmas over its atomic constraints."""
    from z3 import is_le, is_ge, is_lt, is_gt
    D = S.ir.get("derivations") or {}
    if not D:
        return None
    subj = {k: (r.get("subject") or (None, None))[1] for k, r in S.ir["requirements"].items()}
    gl_all = {k: f for k, f in S.R.items() if is_glossary(k)}

    def definitions(keep=()):
        """Glossary conjuncts of the form  v == e  (v not in e) are definitions: they are substituted into every
        formula, which keeps quantifier elimination on nonlinear physics tractable. Variables in `keep` (shared
        quantities of an interface) are not substituted."""
        from z3 import is_eq as _iseq, is_const, substitute as _sub
        conj = [(k, c) for k, f in gl_all.items() for c in (f.children() if f.decl().name() == "and" else [f])]
        defs = []
        for k, c in conj:
            if _iseq(c):
                for v, e in ((c.arg(0), c.arg(1)), (c.arg(1), c.arg(0))):
                    if is_const(v) and str(v) not in free_consts(e) and str(v) not in keep and str(v) in S.vars:
                        defs.append((k, c, v, e)); break
        sub = [(v, e) for _, _, v, e in defs]
        for _ in range(len(sub)):                 # close the substitution under itself
            sub = [(v, _sub(e, *sub)) for v, e in sub]
        dropped = {id(c) for _, c, _, _ in defs}
        gl = {}
        for k, f in gl_all.items():
            cs = [c for c in (f.children() if f.decl().name() == "and" else [f]) if id(c) not in dropped]
            cs = [c for c in cs if not any(c.eq(dc) for _, dc, _, _ in defs)]
            gl[k] = _sub(And(*cs), *sub) if sub and cs else (And(*cs) if cs else BoolVal(True))
        return (lambda f: _sub(f, *sub) if sub else f), gl

    expand, gl = definitions()
    A = And(S.domain, *gl.values())
    reals = lambda f: sorted((v for n, v in free_consts(f).items() if S.vtype.get(n) not in ("Boolean",)), key=str)
    out = {}
    for name, d in D.items():
        P, kids = expand(S.R[d["original"]]), {k: expand(S.R[k]) for k in d["derived"]}
        r = dict(original=d["original"], derived=list(kids))
        ref = refines(P, list(kids.values()), A)
        r["valid"] = ref["valid"]
        r["children_consistent"] = ref.get("children_consistent")
        # static (design-space) refinement: the children are jointly satisfiable under A and imply the parent.
        # Reactive (input/output) refinement additionally needs input-totality: for every admissible input there is
        # an output meeting the children; it is checked only when the requirements declare outputs ('out').
        attrs = [a_ for k in [d["original"]] + list(kids) for a_ in S.ir["requirements"][k]["attrs"]]
        outs = sorted({a_["name"] for a_ in attrs if a_["dir"] == "out"})
        r["static_refinement"] = bool(ref["valid"] and ref.get("children_consistent"))
        if not outs:
            r["kind"] = "static"
            r["input_total"] = "not applicable (no output attributes declared)"
        else:
            r["kind"] = "reactive"
            r["input_total"] = input_total(And(A, *kids.values()), A, [S.vars[n] for n in outs])
            r["reactive_refinement"] = bool(ref["valid"] and r["input_total"])
        # worst case of the bounded quantity of the parent (parent of the form  q <= c  or  c >= q)
        q = None
        if is_le(P) or is_lt(P):
            q = P.arg(0)
        elif is_ge(P) or is_gt(P):
            q = P.arg(1)
        if q is not None:
            r["bounded_quantity"] = str(q)
            r["worst_case"] = _sup(q, And(A, *kids.values()))
        # abduction by replacement
        ab = {}
        ids = list(kids)
        for size in (1, 2):
            for drop in itertools.combinations(ids, size):
                voc = sorted({v for k in drop for v in reals(kids[k])}, key=str)
                rest = [kids[k] for k in ids if k not in drop]
                a = _abduce_bounded(P, rest, A, voc)
                ab[" + ".join(drop)] = dict(vocabulary=[str(v) for v in voc], replacement=a["W"], method=a["method"],
                                            exists=is_sat(A, *rest, a["W_expr"])[0] if a["W_expr"] is not None else None)
        r["abduction"] = ab
        # interface contracts: one subsystem (subject type) against the rest and the negated parent
        groups = sorted({subj[k] for k in ids if subj[k]} - {subj[d["original"]]})
        itf = {}
        for gname in groups:
            raw_a = And(*[S.R[k] for k in ids if subj[k] == gname], *[f for k, f in gl_all.items() if subj[k] == gname])
            raw_b = And(*[S.R[k] for k in ids if subj[k] != gname], *[f for k, f in gl_all.items() if subj[k] != gname],
                        Not(S.R[d["original"]]))
            keep = set(free_consts(raw_a)) & set(free_consts(raw_b))
            ex2, gl2 = definitions(keep)
            fa = And(*[ex2(S.R[k]) for k in ids if subj[k] == gname], *[f for k, f in gl2.items() if subj[k] == gname])
            fb = And(S.domain, *[ex2(S.R[k]) for k in ids if subj[k] != gname],
                     *[f for k, f in gl2.items() if subj[k] != gname], Not(ex2(S.R[d["original"]])))
            shared = sorted(set(free_consts(fa)) & set(free_consts(fb)))
            e = dict(subsystem=gname, shared=shared)
            if is_sat(fa, fb)[0]:
                e["contract"] = None
                e["note"] = "no interface contract exists: the subsystem's requirements and the rest of the allocation admit a violation of the parent"
            else:
                I = _interpolate_bounded(fa, fb, [S.vars[n] for n in shared])
                e.update(strongest=I["strongest"], weakest=I["weakest"])
                if len(shared) == 1:
                    # one shared quantity v: the contracts form the interval of upper bounds on v between what the
                    # subsystem guarantees (sup of v under its requirements) and what the rest tolerates (the
                    # largest c such that v = c can never violate the parent); their difference is the margin
                    from z3 import substitute, RealVal
                    v = S.vars[shared[0]]
                    s_max = _sup(v, fa)
                    tol = lambda c: _unsat(substitute(fb, (v, RealVal(c))))   # 'unknown' is not tolerated
                    w_max = None
                    if s_max is not None and tol(s_max):
                        lo, hi = s_max, s_max * 2 + 1
                        while tol(hi) and hi < 1e15:
                            lo, hi = hi, hi * 2
                        for _ in range(200):
                            mid = (lo + hi) / 2
                            lo, hi = (mid, hi) if tol(mid) else (lo, mid)
                            if hi - lo <= 1e-12 * max(1.0, abs(hi)):
                                break
                        w_max = lo
                    e.update(strongest_bound=s_max, weakest_bound=w_max,
                             margin=(w_max - s_max) if s_max is not None and w_max is not None else None)
            itf[gname] = e
        r["interfaces"] = itf
        # discretisation into Boolean lemmas over the atomic constraints of the derivation
        atoms = []
        for f in list(kids.values()) + [P]:
            _atoms(f, atoms)
        feas = [bits for bits in itertools.product([0, 1], repeat=len(atoms))
                if not _unsat(A, *[a if b else Not(a) for a, b in zip(atoms, bits)])]   # 'unknown' kept as feasible
        try:
            from sympy import symbols
            from sympy.logic import POSform
            sy = symbols(" ".join(f"a{i}" for i in range(len(atoms))))
            sy = sy if isinstance(sy, tuple) else (sy,)
            lemmas = str(POSform(list(sy), [list(b) for b in feas]))
        except Exception as ex:          # sympy missing: report the feasible combinations only
            lemmas = f"(not computed: {ex})"
        r["discretisation"] = dict(atoms={f"a{i}": str(a) for i, a in enumerate(atoms)}, feasible=len(feas),
                                   of=2 ** len(atoms), lemmas=lemmas)
        out[name] = r
        if os.environ.get("SYSMLC_VERBOSE"):
            print(f"[flowdown] {name} done", file=sys.stderr, flush=True)
    return out



# ------------------------------------------------------------------ requirement sets that select an output value
def check_output_groups(S):
    """Requirements of the form  a -> y == e  on an output y that is not the next state of a machine: the same
    circuit reading as for state machines, with y as the bus. Conflicts (two active gates that drive different
    values; pairs suffice because the consequents are equalities, and single requirements whose value the glossary
    excludes are reported as conflicts of size one), holes (situations where no antecedent holds,
    i.e. the line is undriven), overlaps, and sub-formulas that are constant (vacuity)."""
    from z3 import is_eq as _iseq, is_const
    machine_next = {str(S.machine_vars(m)[2]) for m in S.ir["machines"]}
    outs = {a["name"] for r in S.ir["requirements"].values() for a in r["attrs"] if a["dir"] == "out"} - machine_next
    groups = {}
    for k, f in S.R.items():
        if is_glossary(k) or not is_implies(f) or not _iseq(f.arg(1)):
            continue
        a, b = f.arg(1).arg(0), f.arg(1).arg(1)
        y = a if is_const(a) and str(a) in outs else b if is_const(b) and str(b) in outs else None
        if y is not None:
            groups.setdefault(str(y), {})[k] = f
    if not groups:
        return None
    A = And(S.domain, *[f for k, f in S.R.items() if is_glossary(k)])
    out = {}
    for y, reqs in groups.items():
        ins = sorted({v for f in reqs.values() for n, v in free_consts(f).items() if n != y}, key=str)
        C = conflicts(reqs, A, ins, max_size=2)
        cov = coverage({k: f.arg(0) for k, f in reqs.items()}, A)
        dead = {k: dp for k, f in reqs.items() if (dp := dead_parts(f, A))}
        out[y] = dict(requirements=list(reqs), inputs=[str(v) for v in ins], conflicts=C, coverage=cov, constant_subformulas=dead)
    return out
