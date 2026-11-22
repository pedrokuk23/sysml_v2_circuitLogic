"""Logic checks on the IR (z3). Each check runs only if the model has the elements it needs."""
import itertools, os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from z3 import (And, Or, Not, Implies, Exists, ForAll, BoolVal, RealVal, Real, If, simplify, substitute, is_true,
                is_implies, is_eq, is_int_value)
from logic_engine import conflicts, is_sat, valid, qe, finite_region, coverage, free_consts


def bools_in(f, S):
    names = set(free_consts(f))
    return [v for n, v in S.vars.items() if n in names and S.vtype.get(n) == "Boolean"]


def target(f):
    a, b = f.arg(1).arg(0), f.arg(1).arg(1)
    return (b if is_int_value(b) else a).as_long()


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
            a, b = c["requirements"]
            c["repairs"] = {f"{x} cede a {y}": str(Implies(And(g["reqs"][x].arg(0), Not(g["reqs"][y].arg(0))), g["reqs"][x].arg(1)))
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
        res[mname] = dict(enum=g["enum"], cur=str(g["cur"]), next=str(g["nxt"]), inputs=[str(b) for b in ins],
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
            forced = {f: ("OBC" if feas[0][f] else "solo") for f in funs if f not in fixed and all(x[f] == feas[0][f] for x in feas)}
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
        # cut by a cycle does not reach the final node and is not counted (that was a bug in the first version).
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


def run_all(S):
    out = dict(model=S.ir["source"], requirements=list(S.ir["requirements"]))
    if S.ir["machines"]:
        out["machines"] = check_machines(S)
        out["port_contracts"] = check_port_contracts(S, out["machines"])
        out["parents_one_step"] = check_parents_one_step(S)
    v = check_variability(S)
    if v:
        out["variability"] = v
    a = check_actions(S)
    if a:
        out["actions"] = a
    return out
