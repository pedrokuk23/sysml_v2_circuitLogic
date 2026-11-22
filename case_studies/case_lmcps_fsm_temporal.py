#!/usr/bin/env python3
"""Case 1b: does the parent FSM-001 (pullup) follow from its children over time?

Composition (as in the Lockheed Martin Simulink model): the autopilot reads the sensor's previous 'good'
(initially true); the sensor reads the autopilot's MODE (= not TRANSITION) and REQUEST (= TRANSITION or NOMINAL)
of the same step; good = sensor not in FAULT. Transitions: the revised children (conflict-free).
Unspecified situations (holes) are completed by a policy: 'stay' (the model's implicit default), or 'free'
(any next state: what the requirements alone guarantee). The link pullup <-> autopilot in MANEUVER is NOT a
requirement; it is only in the data dictionary ('True when the autopilot is in the MANEUVER state').
We check every version of FSM-001 with and without that glossary axiom, by exhaustive exploration of the finite
product (state x bounded input history), i.e. a complete check, not a bounded one.
"""
import os
import itertools, json

T, N, M, S = "T", "N", "M", "S"
SN, ST, SF = "N", "T", "F"
INPUTS = list(itertools.product([0, 1], repeat=4))   # standby, apfail, supported, limits
H = 6                                                # history length kept for the monitors


def ap_moves(q, sb, af, su, g, policy):
    rules = {T: [(sb, S), (su and g and not sb, N)],
             N: [(sb, S), ((not g) and not sb, M)],
             M: [(sb and g, S), (su and g and not sb, T)],
             S: [((not sb) and not af, T), (af, M)]}[q]
    hit = [t for c, t in rules if c]
    if hit:
        return hit
    return [q] if policy == "stay" else [T, N, M, S]


WEAK = [False]


def sen_moves(q, mode, req, lim, policy):
    fault_exit = ((not req) or (not lim)) if WEAK[0] else ((not req) and not lim)
    rules = {SN: [(lim, SF), ((not req) and not lim, ST)],
             ST: [(req and mode, SN)],
             SF: [(fault_exit, ST)]}[q]
    hit = [t for c, t in rules if c]
    if hit:
        return hit
    return [q] if policy == "stay" else [SN, ST, SF]


def versions(hist, pull):
    """hist[k] = (autopilot, limits) at time t-k (None before time 0). Returns {version: holds_now}."""
    def ap(k): return hist[k] is not None and hist[k][0]
    def li(k): return hist[k] is not None and hist[k][1]
    def pre(k, f, default=False): return f(k) if hist[k] is not None else default
    v1 = (not (li(0) and ap(0))) or pull
    v2 = (not (ap(0) and ap(1) and li(1))) or pull
    # persisted(3,p): p at t, t-1, t-2, t-3 ; preBool(false, preBool(false, !limits)) at time t-k: !limits at t-k-2
    nl2 = lambda k: hist[k + 2] is not None and not hist[k + 2][1]
    v3 = (not (all(ap(k) for k in range(4)) and all(nl2(k) for k in range(4)) and li(1))) or pull
    return dict(v1=v1, v2=v2, v3=v3)


def explore(policy, glossary):
    s0 = (T, SN, True, (None,) * H)
    seen, todo, parent = {s0}, [s0], {s0: None}
    bad = {}
    while todo:
        s = todo.pop(0)
        ap0, sen0, g, hist = s
        for (sb, af, su, li) in INPUTS:
            autop = (not sb) and su and (not af)
            for ap1 in ap_moves(ap0, sb, af, su, g, policy):
                mode, req = ap1 != T, ap1 in (T, N)
                for sen1 in sen_moves(sen0, mode, req, li, policy):
                    nh = ((autop, bool(li)),) + hist[:-1]
                    pulls = [ap1 == M] if glossary else [False, True]
                    for pull in pulls:
                        for v, ok in versions(nh, pull).items():
                            if not ok and v not in bad:
                                bad[v] = (s, (sb, af, su, li), ap1, sen1, pull)
                    n = (ap1, sen1, sen1 != SF, nh)
                    if n not in seen:
                        seen.add(n); parent[n] = (s, (sb, af, su, li)); todo.append(n)
    traces = {}
    for v, (s, inp, ap1, sen1, pull) in bad.items():
        path, x = [], s
        while parent[x] is not None:
            px, pin = parent[x]
            path.append(dict(step_in=dict(zip(["standby", "apfail", "supported", "limits"], pin)), ap=x[0], sensor=x[1]))
            x = px
        path.reverse()
        path.append(dict(step_in=dict(zip(["standby", "apfail", "supported", "limits"], inp)), ap=ap1, sensor=sen1,
                         pullup=pull, violates=v))
        traces[v] = path
    return dict(reachable=len(seen), holds={v: v not in bad for v in ("v1", "v2", "v3")}, counterexamples=traces)


def main():
    res = {}
    for weak in (False, True):
        WEAK[0] = weak
        for policy in ("stay", "free"):
            for gl in (False, True):
                res[f"{'FSM-012weak' if weak else 'FSM-012'}|{policy}{'+glossario' if gl else ''}"] = explore(policy, gl)
    # mutual wait: from (autopilot TRANSITION, sensor FAULT) with the autopilot engaged and limits clear forever
    for weak in (False, True):
        WEAK[0] = weak
        x, seq = (T, SF, False), []
        for _ in range(6):
            ap1 = ap_moves(x[0], 0, 0, 1, x[2], "stay")[0]
            sen1 = sen_moves(x[1], ap1 != T, ap1 in (T, N), 0, "stay")[0]
            x = (ap1, sen1, sen1 != SF); seq.append(x[:2])
        res[f"espera_mutua_{'weak' if weak else 'original'}"] = seq
    json.dump(res, open(os.path.join(os.environ.get("OUT", "."), "case_lmcps_fsm_temporal.json"), "w"), indent=1, default=str)
    for k, v in res.items():
        if k.startswith("espera"):
            print(k, v); continue
        print(k, v["reachable"], v["holds"])
        for ver, tr in v["counterexamples"].items():
            print("  ", ver, "len", len(tr), [(p["ap"], p["sensor"], "".join(str(int(x)) for x in p["step_in"].values())) for p in tr])


if __name__ == "__main__":
    main()
