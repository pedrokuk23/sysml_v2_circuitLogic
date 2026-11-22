#!/usr/bin/env python3
"""Translation-fidelity tests for sysmlc.

A  supported, valid models are accepted and give the published results;
B  invalid models (realistic editing errors) are rejected with a diagnostic, before any analysis;
C  valid SysML v2 that uses constructs the compiler does not translate is rejected, not silently ignored;
D  every statement must be consumed by a rule of the subset grammar: an unknown statement inserted at any
   statement boundary of every model (outside comments) is rejected;
E  statements read only for structure (documentation, subjects, imports, ports, connections, interface usages)
   do not change any analysis result when removed, added or reordered, and inconsistent structure is rejected;
F  every name is declared once in its scope: a second, different declaration of a port definition, part
   definition, variant, state, attribute, ... is rejected, and so is a copy of each of the declarations of the
   models inserted next to the original;
G  the three translations of each requirement (SMT for z3, Verilog for Yosys, Lustre for Kind 2) agree on every
   input valuation of the domain (exhaustive check, independent evaluators for the Verilog and Lustre text).

    python3 tests/run_tests.py            # or: python3 -m pytest tests/run_tests.py
Exit status 0 when every test passes; a JSON summary is written to tests/test_results.json.
"""
import itertools, json, os, re, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
sys.path.insert(0, os.path.join(ROOT, "sysmlc"))
from z3 import Solver, And, Not, sat, is_true, BoolVal, IntVal, substitute, simplify, is_bool  # noqa: E402
from semantics import compile_model, CompileError  # noqa: E402
import analysis, verilog, lustre  # noqa: E402

M = os.path.join(ROOT, "models")
LM = open(os.path.join(M, "lmcps_fsm.sysml")).read()
FS = open(os.path.join(M, "firesat.sysml")).read()
RESULTS = []
MODELS = sorted(f for f in os.listdir(M) if f.endswith(".sysml"))


def record(cls, name, ok, detail=""):
    RESULTS.append(dict(cls=cls, test=name, passed=bool(ok), detail=detail))
    print(f"[{'PASS' if ok else 'FAIL'}] {cls} {name}" + (f" — {detail}" if detail and not ok else ""))


def tmp_model(text):
    f = tempfile.NamedTemporaryFile("w", suffix=".sysml", delete=False)
    f.write(text); f.close()
    return f.name


def rejected(text):
    try:
        compile_model(tmp_model(text))
        return False, "accepted"
    except CompileError as ex:
        return True, "; ".join(ex.errors)
    except Exception as ex:  # any other exception is a crash, not a diagnostic
        return False, f"crash: {type(ex).__name__}: {ex}"


def once(text, old, new):
    assert text.count(old) >= 1, old
    return text.replace(old, new, 1)


# ------------------------------------------------------------------ A: valid models
def class_a():
    S = compile_model(os.path.join(M, "lmcps_fsm.sysml"))
    R = analysis.check_machines(S)
    nconf = {m: len(v["contention"]) for m, v in R.items()}
    holes = {m: sum(h["n"] for h in v["holes"].values()) for m, v in R.items()}
    record("A", "LM model accepted; conflicts 4 + 1", nconf == {"apMachine": 4, "senMachine": 1}, str(nconf))
    record("A", "LM holes 24 + 14", holes == {"apMachine": 24, "senMachine": 14}, str(holes))
    S2 = compile_model(os.path.join(M, "lmcps_fsm_rev.sysml"))
    R2 = analysis.check_machines(S2)
    record("A", "revised LM set accepted and conflict-free", all(len(v["contention"]) == 0 for v in R2.values()),
           str({m: len(v["contention"]) for m, v in R2.items()}))
    F = compile_model(os.path.join(M, "firesat.sysml"))
    V = analysis.check_variability(F)
    record("A", "FireSat: 9 of 32 configurations", (V["n_valid"], V["n_configs"]) == (9, 32), f"{V['n_valid']}/{V['n_configs']}")
    record("A", "FireSat: geo1 dead, leo2 core", V["dead_variants"] == ["orbit.geo1"] and V["core_variants"] == ["orbit.leo2"])
    G = analysis.check_output_groups(compile_model(os.path.join(M, "lmcps_roll_tsm.sysml")))
    ap, ts = G["rollHoldReference"], G["setVal"]
    record("A", "AP-003: conflicts B×D and C×D, vacuous limit clause in A and D",
           sorted(c["requirements"] for c in ap["conflicts"]) == [["AP-003B", "AP-003D"], ["AP-003C", "AP-003D"]]
           and set(ap["constant_subformulas"]) == {"AP-003A", "AP-003D"}, str([c["requirements"] for c in ap["conflicts"]]))
    record("A", "TSM: TSM-002 conflicts with each TSM-003 case; holes for unlisted fault codes",
           len(ts["conflicts"]) == 3 and not ts["coverage"]["complete"])
    G2 = analysis.check_output_groups(compile_model(os.path.join(M, "lmcps_roll_tsm_glossary.sysml")))["setVal"]
    record("A", "TSM with the glossary axiom noFail <=> FC = 0: no conflicts, holes remain", not G2["conflicts"] and not G2["coverage"]["complete"])
    Q = analysis.check_flowdown(compile_model(os.path.join(M, "firesat_flowdown.sysml")))
    r0, r1, rg = Q["resFlow"], Q["resFlowRevised"], Q["geoFlow"]
    record("A", "FireSat flow-down: refinement fails, worst case 31.09 m", (not r0["valid"]) and abs(r0["worst_case"] - 31.09) < 0.01,
           str(r0.get("worst_case")))
    record("A", "FireSat flow-down: revised allocation valid, payload/attitude margin 0.44 urad",
           r1["valid"] and abs(r1["interfaces"]["Payload"]["margin"] - 4.41e-7) < 0.01e-6, str(r1["interfaces"]["Payload"].get("margin")))
    record("A", "FireSat flow-down: no aperture alone and no jitter alone rescues the geostationary concept",
           rg["abduction"]["PAY-2"]["exists"] is False and rg["abduction"]["ADCS-1R"]["exists"] is False)
    p = subprocess.run([sys.executable, os.path.join(ROOT, "sysmlc", "__main__.py"), os.path.join(M, "firesat.sysml"),
                        "-o", tempfile.mkdtemp(), "--no-eda"], capture_output=True, text=True)
    # third-party requirements: NASA Lift+Cruise (mini set), unrolled over time
    import unroll
    from z3 import And as _And
    L = compile_model(os.path.join(ROOT, "models", "third_party", "lpc_mini.sysml"))
    reach = [k for k in L.R if "REACH" in k]; base = [k for k in L.R if k not in reach]
    TB = L.enums["LiftModeKind"].index("thrust_borne")
    t_tb, _ = unroll.earliest(L, base, 14, lambda U, t: U.var("lift_mode", t) == TB)
    r06 = unroll.lasso(L, base + ["LPC_REACH_HOVER_06"], 20)[0]
    r12 = unroll.lasso(L, base + ["LPC_REACH_HOVER_12"], 20)[0]
    record("A", "NASA Lift+Cruise mini set: thrust-borne first at step 11; within 6 ticks unrealizable, within 12 realizable",
           (t_tb, r06, r12) == (11, False, True), str((t_tb, r06, r12)))
    record("A", "CLI exit status 0 on a valid model", p.returncode == 0, p.stderr[-200:])


# ------------------------------------------------------------------ B: invalid models must be rejected
B_CASES = [
    ("misspelled signal in a constraint", LM, "(apState == ApState::T and good and supported)", "(apState == ApState::T and godo and supported)"),
    ("duplicate requirement identifier", LM, "requirement def <'FSM-003'>", "requirement def <'FSM-002'>"),
    ("C-style operator &&", LM, "(apState == ApState::T and good and supported)", "(apState == ApState::T && good and supported)"),
    ("stray character @", LM, "(apState == ApState::T and good and supported)", "(apState == ApState::T and good @ supported)"),
    ("unbalanced parenthesis", LM, "(apState == ApState::T and good and supported)", "(apState == ApState::T and (good and supported)"),
    ("unknown enumeration literal", LM, "implies nextState == ApState::N", "implies nextState == ApState::X"),
    ("conditional without else", FS, "if detectOnBoard ? 5 else 15", "if detectOnBoard ? 5"),
    ("transition to an undeclared state", LM, "first T if standby then S;", "first T if standby then X;"),
    ("undeclared signal in a transition guard", LM, "first T if standby then S;", "first T if standbyy then S;"),
    ("attribute declared with two types", LM, "in attribute good : Boolean;", "in attribute good : Real;"),
    ("two require constraints in one requirement", LM, "require constraint {", "require constraint { true }\n        require constraint {"),
    ("duplicate enumeration literal", LM, "enum T;", "enum T; enum T;"),
    ("missing initial state", LM, "entry; then", "entry; "),
    ("duplicate transition identifier", LM, "transition t03 first T", "transition t02 first T"),
    ("order comparison on an enumeration", LM, "(apState == ApState::T and good and supported)", "(apState < ApState::N and good and supported)"),
    ("comparison of two enumerations", LM, "(apState == ApState::T and good and supported)", "(apState == SenState::F and good and supported)"),
    ("comparison of an enumeration with a number", LM, "(apState == ApState::T and good and supported)", "(apState == 2 and good and supported)"),
    ("comparison of literals of two enumerations", LM, "(apState == ApState::T and good and supported)", "(ApState::M == SenState::F and good and supported)"),
    ("enumeration compared with a literal of another enumeration", LM, "(apState == ApState::T and good and supported)", "(apState != ApState::M and apState == SenState::F and good and supported)"),
    ("comparison of two enumeration attributes of different types", LM, "(apState == ApState::T and good and supported)", "(apState == senState and good and supported)"),
    ("order comparison on an enumeration-valued conditional", LM, "(apState == ApState::T and good and supported)", "((if supported ? ApState::N else ApState::S) < 2 and good and supported)"),
    ("conditional mixing an enumeration and a number", LM, "(apState == ApState::T and good and supported)", "((if supported ? apState else 2) == 2 and good and supported)"),
    ("arithmetic on an enumeration", LM, "(apState == ApState::T and good and supported)", "(apState + 1 == 1 and good and supported)"),
    ("variant with malformed attribute", FS, "variant part gs4 : Ground { attribute redefines maxGap = 100; }", "variant part gs4 : Ground attribute redefines maxGap = 100;"),
]


def class_b():
    for name, base, old, new in B_CASES:
        if old not in base:
            record("B", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base, old, new))
        record("B", name, ok, why)
    bad = tmp_model(once(LM, "and good and supported)", "and godo and supported)"))
    p = subprocess.run([sys.executable, os.path.join(ROOT, "sysmlc", "__main__.py"), bad, "-o", tempfile.mkdtemp()],
                       capture_output=True, text=True)
    record("B", "CLI exits with status 2 and emits no proof", p.returncode == 2 and "godo" in p.stderr, p.stderr[-200:])


# ------------------------------------------------------------------ C: valid SysML v2 outside the translated subset
C_CASES = [
    ("assume constraint in a requirement", LM, "        require constraint {", "        assume constraint { supported }\n        require constraint {", 1),
    ("constraint definition", LM, "enum def ApState", "constraint def Lim { in x : Real; x <= 1 }\n    enum def ApState", 0),
    ("calculation definition", LM, "enum def ApState", "calc def Twice { in x : Real; 2 * x }\n    enum def ApState", 0),
    ("transition with an accept trigger", LM, "transition t02 first T if standby then S;", "transition t02 first T accept go if standby then S;", 0),
    ("entry action in a state", LM, "state T; state N;", "state T { entry action reset; } state N;", 0),
    ("flow connection", LM, "connect sensor.toAp to autopilot.fromSensor;", "flow sensor.toAp to autopilot.fromSensor;", 0),
    ("succession", FS, "then action notify", "succession s1 first archive then action notify", 0),
]


def class_c():
    for name, base, old, new, _ in C_CASES:
        if old not in base:
            record("C", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base, old, new))
        record("C", name, ok and ("unsupported" in why or "not supported" in why or "not of the form" in why), why)


# ------------------------------------------------------------------ D: full consumption
E_CASES = [
    ("unknown statement at package level", LM, "enum def ApState", "garbage blorp;\n    enum def ApState"),
    ("unknown statement inside a requirement", LM, "        require constraint {", "        garbage blorp;\n        require constraint {"),
    ("unknown statement inside a state machine", LM, "state T; state N;", "state T; garbage blorp; state N;"),
    ("unknown statement inside a part definition", LM, "connect sensor.toAp to autopilot.fromSensor;", "connect sensor.toAp to autopilot.fromSensor; garbage blorp;"),
    ("unknown block inside a part definition", LM, "connect sensor.toAp to autopilot.fromSensor;", "connect sensor.toAp to autopilot.fromSensor; blorp zork { }"),
    ("unknown statement inside an enumeration", LM, "enum T;", "enum T; garbage blorp;"),
    ("unknown statement inside a variant", FS, "variant part gs4 : Ground { attribute redefines maxGap = 100; }", "variant part gs4 : Ground { attribute redefines maxGap = 100; garbage blorp; }"),
    ("unknown statement inside an action definition", FS, "then action notify", "garbage blorp; then action notify"),
    ("statement without terminator at the end of a body", LM, "enum T;", "enum T; enum Z"),
]


def boundaries(text):
    """Positions just after every ';' or '{' that is not inside a comment."""
    pos, i, n = [], 0, len(text)
    while i < n:
        if text.startswith("//", i):
            i = text.find("\n", i); i = n if i < 0 else i; continue
        if text.startswith("/*", i):
            i = text.find("*/", i) + 2; continue
        if text[i] in ";{":
            pos.append(i + 1)
        i += 1
    return pos


def class_unknown():
    for name, base, old, new in E_CASES:
        if old not in base:
            record("D", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base, old, new))
        record("D", name, ok and ("unrecognized" in why or "unterminated" in why), why)
    total, missed = 0, []
    for fn in MODELS:
        text = open(os.path.join(M, fn)).read()
        for p in boundaries(text):
            total += 1
            ok, why = rejected(text[:p] + " blorp zork; " + text[p:])
            if not ok:
                missed.append((fn, p, why))
    record("D", f"an unknown statement inserted at each of {total} statement boundaries of the {len(MODELS)} models is rejected", not missed,
           str(missed[:3]))


# ------------------------------------------------------------------ E: structure-only statements
def fingerprint(text):
    S = compile_model(tmp_model(text))
    R = analysis.run_all(S)
    R.pop("model", None)
    # the projected contract is compared through its 'equivalent' flag (equivalence with the asserted contract):
    # z3 may print the same formula with its arguments in another order
    for c in R.get("port_contracts", {}).values():
        c.pop("projection", None)
    return json.dumps(R, sort_keys=True, default=str)


def drop_docs(text):
    return re.sub(r"\bdoc\s*/\*.*?\*/", "", text, flags=re.S)


EXTRA_PART = """
    part def Logger { port tap : ~SensorToAp; }
    part def Probe { port out1 : SensorToAp; }
    part def FSM {"""
F_SAME = [
    ("documentation removed (LM)", LM, drop_docs),
    ("documentation removed (FireSat)", FS, drop_docs),
    ("subjects removed (LM)", LM, lambda t: re.sub(r"\n\s*subject fsm;", "", t)),
    ("unrelated parts, ports and a conjugate connection added (LM)", LM,
     lambda t: once(t, "\n    part def FSM {", EXTRA_PART).replace("satisfy fsm001 by self;",
               "satisfy fsm001 by self;\n        part lg : Logger; part pr : Probe;\n        connect pr.out1 to lg.tap;")),
    ("interface usage renamed (LM)", LM, lambda t: once(t, "interface link : ApSensorLink", "interface link2 : ApSensorLink")),
    ("port definitions moved to the end of the package (LM)", LM,
     lambda t: (lambda m: t.replace(m, "").rstrip().rstrip("}") + "\n" + m + "\n}\n")(
         re.search(r"    port def ApToSensor \{.*?\n    \}\n    port def SensorToAp \{.*?\n    \}\n", t, re.S).group(0))),
]
F_REJECT = [
    ("guard through an undeclared port", LM, "fromSensor.good and supported and not standby", "fromSensr.good and supported and not standby"),
    ("port attribute not in its port definition", LM, "fromSensor.good and supported and not standby", "fromSensor.request and supported and not standby"),
    ("connection to an undeclared port", LM, "connect sensor.toAp to autopilot.fromSensor;", "connect sensor.toAp to autopilot.fromSensr;"),
    ("connection between non-conjugate ports", LM, "connect sensor.toAp to autopilot.fromSensor;", "connect sensor.toAp to autopilot.toSensor;"),
]


def class_structure():
    base = {"LM": fingerprint(LM), "FS": fingerprint(FS)}
    for name, text, f in F_SAME:
        try:
            ok = fingerprint(f(text)) == base["FS" if text is FS else "LM"]
            why = "" if ok else "results differ"
        except CompileError as ex:
            ok, why = False, "; ".join(ex.errors)
        record("E", name + ": same results", ok, why)
    for name, base_t, old, new in F_REJECT:
        if old not in base_t:
            record("E", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base_t, old, new))
        record("E", name + " is rejected", ok, why)


# ------------------------------------------------------------------ F: one declaration per name and scope
PD = "    port def ApToSensor {"
G_CASES = [
    ("port definition declared twice with different attributes", LM, PD, "    port def ApToSensor { out attribute phantom : Boolean; }\n" + PD),
    ("part definition declared twice", LM, "    part def Sensor {", "    part def Sensor { attribute x : Boolean; }\n    part def Sensor {"),
    ("enumeration declared twice", LM, "    enum def ApState", "    enum def ApState { enum Q; }\n    enum def ApState"),
    ("interface definition declared twice", LM, "    interface def ApSensorLink", "    interface def ApSensorLink { end a : ApToSensor; }\n    interface def ApSensorLink"),
    ("requirement definition name reused under another identifier", LM, "requirement def <'FSM-003'> ApTtoN", "requirement def <'FSM-003'> ApTtoS"),
    ("attribute declared twice in a port definition", LM, "out attribute mode : Boolean;", "out attribute mode : Boolean; out attribute mode : Boolean;"),
    ("port declared twice in a part", LM, "port toSensor : ApToSensor;", "port toSensor : ApToSensor; port toSensor : SensorToAp;"),
    ("port name reused in another part", LM, "port toAp : SensorToAp;", "port toAp : SensorToAp; port toSensor : SensorToAp;"),
    ("state machine declared twice in a part", LM, "exhibit state senMachine", "exhibit state apMachine"),
    ("state declared twice", LM, "state T; state N;", "state T; state N; state T;"),
    ("part usage declared twice in the system part", FS, "        part comm : CommChoice;", "        part comm : CommChoice;\n        part comm : BusChoice;"),
    ("attribute declared twice in a part definition", FS, "attribute h : Real; attribute period : Real;", "attribute h : Real; attribute period : Real; attribute h : Integer;"),
    ("variation declared twice", FS, "    variation part def BusChoice :> Bus {", "    variation part def BusChoice :> Bus { variant part bigBus : Bus { attribute redefines payloadCapacity = 900; } }\n    variation part def BusChoice :> Bus {"),
    ("variant declared twice in a variation", FS, "variant part midBus   : Bus {", "variant part smallBus : Bus { attribute redefines payloadCapacity = 1; }\n        variant part midBus   : Bus {"),
    ("attribute redefined twice in a variant", FS, "attribute redefines payloadCapacity = 100;", "attribute redefines payloadCapacity = 100; attribute redefines payloadCapacity = 999;"),
    ("action definition declared twice", FS, "    action def DetectAndReport {", "    action def DetectAndReport { first start; then done; }\n    action def DetectAndReport {"),
    ("two system parts", FS, "    part def FireSatSystem {", "    part def Other { part obc; allocate x to obc; }\n    part def FireSatSystem {"),
]


def class_duplicates():
    for name, base, old, new in G_CASES:
        if old not in base:
            record("F", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base, old, new))
        record("F", name + " is rejected", ok and ("duplicate" in why or "more than once" in why or "two system" in why), why)
    import parser as P
    total, missed = 0, []
    for fn in MODELS:
        text = open(os.path.join(M, fn)).read()
        _, _, decls = P.walk_model(text)
        for s0, s1, ctx, nm in decls:
            total += 1
            ok, why = rejected(text[:s1] + text[s0:s1] + text[s1:])
            if not ok or "duplicate" not in why:
                missed.append((fn, ctx, nm, why[:80]))
    record("F", f"a copy of each of the {total} declarations of the {len(MODELS)} models is rejected as a duplicate", not missed,
           str(missed[:3]))


# ------------------------------------------------------------------ G: SMT = Verilog = Lustre on every valuation
def py_from_verilog(e):
    e = e.replace("&&", " and ").replace("||", " or ")
    e = re.sub(r"!(?!=)", " _not", e)          # !(x) -> _not(x), keeps Verilog precedence
    return e


def py_from_lustre(e):
    e = re.sub(r"\bv_", "", e)
    e = e.replace("=>", " @IMP@ ").replace("<>", "!=")
    e = re.sub(r"(?<![<>=!])=(?!=)", "==", e)
    return e.replace("@IMP@", "<=")       # implication on fully parenthesized Booleans: a <= b


def class_cross():
    S = compile_model(os.path.join(M, "lmcps_fsm.sysml"))
    out = tempfile.mkdtemp()
    verilog.emit_design(S, out)
    vtext = open(os.path.join(out, "reqs.v")).read()
    vexp = {m.group(1): m.group(2) for m in re.finditer(r"assign r_(\w+) = (.*);", vtext)}
    dtext = open(os.path.join(out, "design.sv")).read()   # the assertions Yosys proves, one per requirement
    vexp.update({m.group(1): m.group(2) for m in re.finditer(r"`ifdef P_(\w+)\s*\n\s*always @\* assert \((.*)\);", dtext)})
    lustre.emit(S, os.path.join(out, "design.lus"))
    ltext = open(os.path.join(out, "design.lus")).read()
    lexp = {m.group(1): m.group(2) for m in re.finditer(r"ok_(\w+) = (.*);", ltext)}
    total, bad = 0, []
    for k, f in S.R.items():
        tag = re.sub(r"\W", "_", k)
        names = sorted(set(re.findall(r"[A-Za-z_]\w*", vexp[tag])))
        ranges = []
        for n in names:
            ty = S.vtype.get(n)
            ranges.append(range(len(S.enums[ty])) if ty in S.enums else (False, True))
        for vals in itertools.product(*ranges):
            env = dict(zip(names, vals))
            sub = [(S.vars[n], BoolVal(v) if isinstance(v, bool) else IntVal(v)) for n, v in env.items()]
            zv = is_true(simplify(substitute(f, *sub)))
            vv = bool(eval(py_from_verilog(vexp[tag]), {"_not": lambda x: not x}, {n: int(v) if not isinstance(v, bool) else v for n, v in env.items()}))
            ok = zv == vv
            if tag in lexp:
                lv = bool(eval(py_from_lustre(lexp[tag]), {}, dict(env)))
                ok = ok and lv == zv
            total += 1
            if not ok:
                bad.append((k, env))
    record("G", f"SMT, Verilog and Lustre agree on {total} valuations of {len(S.R)} requirements", not bad, str(bad[:3]))


# ------------------------------------------------------------------ H: front end = Pilot Implementation AST
def class_ast():
    import ast_check
    d = ast_check.AST
    if not os.path.isdir(d):
        record("H", "Pilot AST dumps present", False, "run validation/dump_ast.sh"); return
    for m in sorted(f[:-5] for f in os.listdir(d) if f.endswith(".json") and f not in ("ast_check.json", "frontend_check.json")):
        n, ne, fails = ast_check.check(m)
        record("H", f"{m}: sysmlc IR = Pilot AST ({n} comparisons, {ne} expressions equivalent)", not fails, "; ".join(fails[:3]))
    import frontend_check
    for m in sorted(f[:-5] for f in os.listdir(d) if f.endswith(".json") and f not in ("ast_check.json", "frontend_check.json")):
        r = frontend_check.check(m)
        record("H", f"{m}: every analysis gives the same results through the Pilot front end ({r['leaves']} result "
               f"leaves; {r['leaves'] - r['identical']} equal up to formula printing or the QE time limit)",
               not r["failures"], "; ".join(r["failures"][:3]))


def test_all():
    for f in (class_a, class_b, class_c, class_unknown, class_structure, class_duplicates, class_cross, class_ast):
        f()
    assert all(r["passed"] for r in RESULTS)


if __name__ == "__main__":
    for f in (class_a, class_b, class_c, class_unknown, class_structure, class_duplicates, class_cross, class_ast):
        try:
            f()
        except Exception as ex:
            record(f.__name__, "suite raised", False, f"{type(ex).__name__}: {ex}")
    n = sum(r["passed"] for r in RESULTS)
    json.dump(dict(passed=n, total=len(RESULTS), tests=RESULTS), open(os.path.join(HERE, "test_results.json"), "w"), indent=1)
    print(f"\n{n}/{len(RESULTS)} tests passed")
    sys.exit(0 if n == len(RESULTS) else 1)
