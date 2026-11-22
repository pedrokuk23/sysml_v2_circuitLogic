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
H  the front end agrees with the AST of the SysML v2 Pilot Implementation;
I  regressions for the semantic contract (20 tests): undeclared types, non-Boolean constraints and Boolean/number coercions are
   rejected; two machines over one enumeration are rejected rather than bound by guess; a solver answer UNKNOWN
   yields 'inconclusive' and never an equivalence, a refutation or an absence; static and reactive refinement are
   distinguished (C = x and y refines P = y statically, not reactively); a single requirement that the glossary
   contradicts is reported as a conflict of size one.

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
    st_tb, t_tb, _ = unroll.earliest(L, base, 14, lambda U, t: U.var("lift_mode", t) == TB)
    r06 = unroll.trace(L, base + ["LPC_REACH_HOVER_06"], 6)[0]
    r12 = unroll.lasso(L, base + ["LPC_REACH_HOVER_12"], 20)[0]
    record("A", "NASA Lift+Cruise mini set: thrust-borne first at step 11; within 6 ticks refuted (UNSAT), within 12 a lasso (SAT)",
           (st_tb, t_tb, r06, r12) == ("sat", 11, "unsat", "sat"), str((st_tb, t_tb, r06, r12)))
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


# ------------------------------------------------------------------ I: semantic contract regressions
ROLL = open(os.path.join(M, "lmcps_roll_tsm.sysml")).read()
FX = os.path.join(HERE, "fixtures")
I_REJECT = [
    ("undeclared type Reel", ROLL, "in attribute turnKnob : Real;", "in attribute turnKnob : Reel;"),
    ("numeric require constraint { x + 1 }", ROLL,
     "require constraint { (rollAngle < 6.0 and rollAngle > -6.0) implies rollHoldReference == 0.0 }",
     "require constraint { rollAngle + 1.0 }"),
    ("Boolean in arithmetic (good + 1 > 0)", LM, "(apState == ApState::T and good and supported)",
     "(apState == ApState::T and good + 1.0 > 0.0 and supported)"),
    ("Boolean compared with a number (good == 1)", LM, "(apState == ApState::T and good and supported)",
     "(apState == ApState::T and good == 1.0 and supported)"),
    ("number used as a Boolean operand", ROLL, "(rollAngle < 6.0 and rollAngle > -6.0) implies",
     "(rollAngle and rollAngle > -6.0) implies"),
    ("numeric guard of a transition", LM, "transition t02 first T if standby then S;",
     "transition t02 first T if 1.0 + 1.0 then S;"),
]


def class_regressions():
    for name, base, old, new in I_REJECT:
        if old not in base:
            record("I", name, False, "test fixture does not apply"); continue
        ok, why = rejected(once(base, old, new))
        record("I", f"rejected: {name}", ok, why)
    ok, why = rejected(open(os.path.join(FX, "two_machines_same_enum.sysml")).read())
    record("I", "rejected: two machines over one enumeration (ambiguous current/next binding)",
           ok and "cannot be bound unambiguously" in why, why)
    S1 = compile_model(os.path.join(FX, "one_machine.sysml"))
    record("I", "accepted: one machine, binding state1/next1", str(S1.machine_vars("m1")[1:]) == "(state1, next1)")
    # solver UNKNOWN is never read as a conclusion
    import unroll, z3
    import logic_engine

    class Unknown(z3.Solver):
        def check(self, *a):
            return z3.unknown

        def reason_unknown(self):
            return "forced by the test"
    L = compile_model(os.path.join(M, "third_party", "lpc_mini.sysml"))
    keys = [k for k in L.R if "REACH" not in k]
    real = unroll.Solver
    unroll.Solver = Unknown
    try:
        st_t = unroll.trace(L, keys, 3)[0]
        st_l = unroll.lasso(L, keys, 4)[0]
        st_e = unroll.earliest(L, keys, 3, lambda U, t: z3.BoolVal(True))[0]
        k1 = [k for k in keys if "STAY_ON" in k][:2]
        st_q = unroll.equivalent_over(L, k1[0], k1[1], 2)[0] if len(k1) == 2 else "unknown"
        rc, unk = unroll.reachable_conflicts(L, keys, [k for k in keys if "_TO_" in k][:2], 1)
    finally:
        unroll.Solver = real
    record("I", "UNKNOWN in unrolling: trace, lasso, earliest and equivalence report 'unknown', no conflict concluded",
           (st_t, st_l, st_e, st_q) == ("unknown",) * 4 and rc == [] and len(unk) >= 1, str((st_t, st_l, st_e, st_q, rc)))
    sys.path.insert(0, os.path.join(ROOT, "experiments", "third_party"))
    import lpc
    unroll.Solver = Unknown
    try:
        r = lpc.realizability(L, keys + [k for k in L.R if "REACH" in k][:1], 4, 4)
    finally:
        unroll.Solver = real
    record("I", "UNKNOWN in the Lift+Cruise checks: realizability 'inconclusive', no finite refutation",
           r["verdict"] == "inconclusive" and "no_trace_of_steps" not in r, str(r)[:200])
    real_le = logic_engine.Solver
    logic_engine.Solver = Unknown
    try:
        logic_engine.is_sat(z3.Bool("p"))
        raised = False
    except logic_engine.Inconclusive:
        raised = True
    finally:
        logic_engine.Solver = real_le
    record("I", "UNKNOWN in the static analyses raises Inconclusive (no SAT/UNSAT reading)", raised)
    R = analysis.check_flowdown(compile_model(os.path.join(FX, "static_vs_reactive.sysml")))["f"]
    record("I", "C = x and y, P = y: static refinement holds, reactive refinement fails (not input-total)",
           R["static_refinement"] is True and R["input_total"] is False and R["reactive_refinement"] is False, str(R)[:200])
    # reactive refinement against an independent oracle, on the original relation (no substitution of definitions)
    expected = dict(a_true=(True, True, True), b_none=(True, False, False), c_x_eq_y=(True, False, False),
                    d_y_eq_x=(True, False, False), e_false=(False, True, False))
    got = {}
    for n in sorted(expected):
        r = analysis.check_flowdown(compile_model(os.path.join(FX, "refinement_controls", n + ".sysml")))["f"]
        got[n] = (r["static_refinement"], r["input_total"], r["reactive_refinement"])
    record("I", "five refinement controls (A = true, none, x == y, y == x, false; C = y or x and y; P = y): static, "
                "input-total and reactive refinement as the oracle; the form of an equality does not matter",
           got == expected, str(got))
    import z3 as _z3
    _real = _z3.Solver
    _z3.Solver = Unknown
    try:
        analysis.reachable_situations(compile_model(os.path.join(M, "lmcps_fsm.sysml")), {})
        comp = "decided"
    except logic_engine.Inconclusive:
        comp = "inconclusive"
    finally:
        _z3.Solver = _real
    record("I", "UNKNOWN in the reachable-state enumeration and the composition checks gives Inconclusive, "
                "not a deterministic or total composition", comp == "inconclusive", comp)
    logic_engine.Solver = Unknown
    try:
        x_, y_ = z3.Bools("x y")
        ref = logic_engine.refines(y_, [And(x_, y_)])
        try:
            fd = analysis.check_flowdown(compile_model(os.path.join(FX, "static_vs_reactive.sysml")))["f"]["implication"]
        except logic_engine.Inconclusive:
            fd = "inconclusive (raised)"
    finally:
        logic_engine.Solver = real_le
    record("I", "UNKNOWN in a refinement: implication and consistency inconclusive (None), never 'fails'",
           ref["valid"] is None and ref["children_consistent"] is None and fd.startswith("inconclusive"), f"{ref} {fd}")
    # abduction: every reported replacement is certified sufficient (A & rest & W & not P is UNSAT)
    w_, x_ = z3.Reals("w x")
    r1 = analysis._abduce_bounded(w_ <= 1, [], BoolVal(True), [w_])
    s_ = z3.Solver(); s_.add(r1["W_expr"], Not(w_ <= 1))
    ab = [analysis.check_flowdown(compile_model(os.path.join(FX, "abduction", n)))["f"]["abduction"]["C"]
          for n in ("child_w_le_2.sysml", "child_w_le_0.sysml")]
    record("I", "abduction with nothing to eliminate (P: w <= 1, C: w <= 2 or w <= 0): replacement w <= 1, "
                "certified sufficient and weakest, through the API and the models",
           s_.check() == z3.unsat and str(r1["W"]) == "w <= 1"
           and all(a_["certification"] == "sufficient" and a_["weakest"] is True for a_ in ab), f"{r1['W']} {ab}")
    real_tac = z3.Tactic

    def no_qe(*a, **k):
        raise z3.Z3Exception("quantifier elimination disabled by the test")
    z3.Tactic = no_qe
    try:
        far = analysis._abduce_bounded(w_ <= 1e11, [x_ == w_], BoolVal(True), [w_])
        third = analysis._abduce_bounded(3 * w_ <= 1, [x_ == w_], BoolVal(True), [w_])
        logic_engine.Solver = Unknown
        try:
            allunk = analysis._abduce_bounded(w_ <= 1, [x_ == w_], BoolVal(True), [w_])
        finally:
            logic_engine.Solver = real_le
    finally:
        z3.Tactic = real_tac
    record("I", "numerical abduction: a threshold beyond the grid gives no candidate (True is rejected as "
                "insufficient); w <= 1/3 gives a certified conservative bound; a grid answered UNKNOWN gives no "
                "candidate and counts the inconclusive points",
           far["W"] is None and far.get("certification") == "insufficient"
           and third["certification"] == "sufficient" and third["W"] == "w <= 333333/1000000"
           and allunk["W"] is None and allunk.get("inconclusive_points", 0) > 100, f"{far['method']} | {third['W']} | {allunk['method']}")
    # command line: an analysis that depends on UNKNOWN ends with status 'inconclusive' and exit code 3
    import importlib.util
    spec = importlib.util.spec_from_file_location("sysmlc_main", os.path.join(ROOT, "sysmlc", "__main__.py"))
    cli = importlib.util.module_from_spec(spec); spec.loader.exec_module(cli)

    def run_cli(model, unknown):
        out = tempfile.mkdtemp()
        argv = sys.argv
        sys.argv = ["sysmlc", model, "-o", out, "--no-eda"]
        if unknown:
            logic_engine.Solver = Unknown
        try:
            cli.main(); code = 0
        except SystemExit as ex:
            code = ex.code
        finally:
            sys.argv = argv
            logic_engine.Solver = real_le
        res = json.load(open(os.path.join(out, "results.json")))
        return code, res.get("status"), bool(res.get("reason") or res.get("inconclusive"))
    fx = os.path.join(FX, "static_vs_reactive.sysml")
    c0, c1 = run_cli(fx, False), run_cli(fx, True)
    record("I", "command line: normal run 'complete' with exit 0; under UNKNOWN 'inconclusive' with a reason and "
                "exit 3", c0[:2] == (0, "complete") and c1 == (3, "inconclusive", True), f"{c0} {c1}")
    F = analysis.check_flowdown(compile_model(os.path.join(M, "firesat_flowdown.sysml")))
    record("I", "FireSat flow-downs are static (no output attributes)", all(v["kind"] == "static" for v in F.values()))
    G = analysis.check_output_groups(compile_model(os.path.join(FX, "unit_conflict.sysml")))
    record("I", "unit conflict (y <= 0 and x -> y == 1) reported as a conflict of size one",
           G["y"]["conflicts"] == [dict(requirements=["R1"], region="x")], str(G["y"]["conflicts"]))


def test_all():
    for f in (class_a, class_b, class_c, class_unknown, class_structure, class_duplicates, class_cross, class_ast,
              class_regressions):
        f()
    assert all(r["passed"] for r in RESULTS)


if __name__ == "__main__":
    for f in (class_a, class_b, class_c, class_unknown, class_structure, class_duplicates, class_cross, class_ast,
              class_regressions):
        try:
            f()
        except Exception as ex:
            record(f.__name__, "suite raised", False, f"{type(ex).__name__}: {ex}")
    n = sum(r["passed"] for r in RESULTS)
    json.dump(dict(passed=n, total=len(RESULTS), tests=RESULTS), open(os.path.join(HERE, "test_results.json"), "w"), indent=1)
    print(f"\n{n}/{len(RESULTS)} tests passed")
    sys.exit(0 if n == len(RESULTS) else 1)
