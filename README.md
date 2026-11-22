# sysmlc — Systems Models as Logic Circuits

Code, models and data for the article

> P. Kukulka de Albuquerque and P. R. B. Cardoso, "Systems Models as Logic Circuits: Compiling a SysML v2 Subset into Digital Logic
> for Analysis," submitted to *Software and Systems Modeling*, 2026.

Repository: https://github.com/pedrokuk23/sysml_v2_circuitLogic

`sysmlc` reads a subset of the SysML v2 textual notation and compiles it to:
- SMT formulas, in Z3;
- Verilog, for the Yosys synthesis suite;
- Lustre, for Kind 2.

It then runs the logic operations of the paper:
- refinement, conflicts (bus contention), holes (undriven lines) and priority repair;
- port contracts as interpolants;
- variability as a configuration circuit (dead and core variants) and allocation backbones;
- action-flow token games;
- k-induction and IC3/PDR proofs;
- the semantic difference (miter) between two versions of a requirement set.

## Installation

Tested with Python 3.13 on Linux.

```
pip install -r requirements.txt     # z3, sympy, Yosys (WebAssembly build), matplotlib, Pacti, flamapy
```

- **Required:** [Graphviz](https://graphviz.org) (`dot`) on the PATH.
- **Optional:**
  - [OCRA](https://ocra.fbk.eu) 2.1 (FBK licence, not redistributed here), with `OCRA=/path/to/ocra-linux64`;
  - [Kind 2](https://github.com/kind2-mc/kind2/releases) v2.2.0, with `KIND2=/path/to/kind2` (and `Z3_BIN=/path/to/z3` if needed);
  - Java 17 and the SysML v2 Pilot Implementation 0.63.1, for the syntax check (`SYSML_KERNEL_DIR`, see `validation/`).

## Reproducing the paper

```
sh scripts/run_all.sh        # about 15 min; outputs in results/out/, reference outputs in results/reference/
```

Or step by step:

| Paper item | Command | Reference output |
|---|---|---|
| Lockheed Martin model: conflicts C1–C5, holes 24 + 14 (16 + 9 in the situations the reference design reaches), reachable states, port contract, proofs, IC3/PDR invariant  | `python3 sysmlc/__main__.py models/lmcps_fsm.sysml -o results/out/lmcps` | `results/reference/lmcps/REPORT.md`, `results.json`, `design.sv`, `reqs.v` |
| FireSat: 9 of 32 configurations, dead `geo1`, core `leo2`, allocation, action flow  | `python3 sysmlc/__main__.py models/firesat.sysml -o results/out/firesat` | `results/reference/firesat/` |
| FireSat quantitative flow-down along `#refinement` dependencies: refinement and worst case, abduction by replacement, interface contracts and margins, discretisation, geostationary concept | `python3 sysmlc/__main__.py models/firesat_flowdown.sysml -o results/out/firesat_flowdown --no-eda` | `results/reference/firesat_flowdown/` |
| Roll-hold reference AP-003A–D and triplex signal monitor TSM-002/003 (real-valued requirement sets): conflicts, holes, vacuous clauses; variant with the glossary axiom noFail ⇔ FC = 0 | `python3 sysmlc/__main__.py models/lmcps_roll_tsm.sysml -o results/out/lmcps_roll_tsm --no-eda` (and `_glossary`) | `results/reference/lmcps_roll_tsm/`, `lmcps_roll_tsm_glossary/` |
| Semantic difference between the original and revised requirements | `python3 sysmlc/diff.py models/lmcps_fsm.sysml models/lmcps_fsm_rev.sysml -o results/out/diff` | `results/reference/diff/diff.json` |
| Scalability sweep | `OUT=results/out python3 sysmlc/bench_scale.py` | `results/reference/bench_scale.json` |
| Independent cross-check of the FireSat flow-down and of AP-003/TSM on hand-written formulas (same results as the compiler) | `OUT=results/out python3 case_studies/case_firesat2.py`, `case_lmcps_roll.py` | `results/reference/case_studies/` |
| FSM-001 temporal versions; hypotheses of the proof; 5 of 34 holds | `OUT=results/out python3 case_studies/case_lmcps_fsm_temporal.py`, then `case_lmcps_fsm_holes.py` | `case_lmcps_fsm_temporal.json`, `case_lmcps_fsm_holes.json` |
| Original FRET requirement set (needs `sh scripts/fetch_external.sh`) | `OUT=results/out python3 case_studies/case_lmcps_fsm.py` | `case_lmcps_fsm.json` |
| Translation-fidelity tests: 117 tests in nine classes, including an unknown statement inserted at all 701 statement boundaries of the six models, changes to structure-only statements, a copy of each of the 664 declarations, and (class H) agreement of the compiler's IR, and of every analysis result, with the SysML v2 Pilot Implementation's syntax tree, and (class I) regressions for type checking, unambiguous machine binding, SAT/UNSAT/UNKNOWN handling (unrolling, composition, refinement), static versus reactive refinement against an oracle, certified abduction candidates and conflicts of size one | `python3 tests/run_tests.py` | `tests/test_results.json` |
| Defect injection on FSM-002–013 of the original and of the revised set: 90 and 98 meaning-changing and 53 and 57 meaning-preserving mutants; miter vs IC3/PDR vs Kind 2; full conflict and hole regions compared (68/90 and 66/98 change) | `KIND2=... python3 experiments/mutation.py -o results/out/mutation` and `... --model models/lmcps_fsm_rev.sysml -o results/out/mutation_rev`, then `python3 experiments/mutation_regions.py --json results/out/mutation/mutation.json` (and `--model models/lmcps_fsm_rev.sysml --json results/out/mutation_rev/mutation.json`) | `results/reference/mutation/mutation.json`, `results/reference/mutation_rev/mutation.json` |
| Each Lockheed Martin conflict can be forced by the environment against every requirement-compliant controller (attractor of the safety game) | `python3 experiments/forced_conflicts.py` | `results/reference/case_studies/forced_conflicts.json` |
| Kind 2 realizability, the FRET back end  | `cd baselines/kind2 && python3 iterate.py` | `results/reference/kind2/kind2_results.json` |
| Kind 2 model checking of the compiled design | `python3 sysmlc/lustre.py models/lmcps_fsm.sysml results/out/kind2` | `results/reference/kind2/kind2.json`, `design.lus` |
| Pacti contract quotient | `cd baselines/pacti && python3 firesat_pacti.py` | `results/reference/pacti/pacti_results.json` |
| flamapy feature-model analysis | `cd baselines/flamapy && python3 fm.py` | `results/reference/flamapy/` |
| SysML v2 syntax check (0 errors, 0 warnings) | `SYSML_KERNEL_DIR=... sh validation/validate.sh` | `validation/validation_0.63.1.log` |
| Pilot Implementation syntax tree of each model (input of test class H) | `SYSML_KERNEL_DIR=... sh validation/dump_ast.sh` | `results/reference/ast/*.json` |
| Every analysis through the second front end (Pilot syntax tree): same results on the six models | `python3 tests/frontend_check.py`; or `python3 -m sysmlc MODEL --frontend pilot` | `results/reference/ast/frontend_check.json` |
| Front end vs Pilot syntax tree: 403 comparisons, 107 expressions proved equivalent, 515 of 541 perturbed trees told apart | `python3 tests/ast_check.py` | `results/reference/ast/ast_check.json` |
| OCRA 2.1 contract refinement: FireSat flow-down (angular form) and LM port contract / FSM-001 | `OCRA=/path/to/ocra-linux64 python3 baselines/ocra/ocra_baseline.py` | `results/reference/ocra/ocra_results.json`, `*.oss` |
| Third-party requirements: NASA Lift+Cruise (FRET case study) translated from FRET's past-time semantics to SysML v2 (`models/third_party/lpc_{mini,full}.sysml`) and checked on the unrolled circuit; reproduces NASA's published results (mode jump without stay requirements, equivalence of the stay formalizations, thrust-borne first at step 11, within 10 ticks unrealizable / 11 realizable, wind results) | `python3 experiments/third_party/fret2sysml.py FRET.json OUT.sysml`; `python3 experiments/third_party/lpc.py` | `results/reference/third_party/lpc_results.json` |
| Validation of the FRET-to-SysML translation against FRET's own Lustre (CoCoSpec) code: every requirement equivalent on all traces of 21 steps (each verdict from an UNSAT answer; UNKNOWN would be reported as inconclusive) | `python3 experiments/third_party/validate_translation.py FRET.json MODEL.sysml 20` | `results/reference/third_party/translation_validation_{mini,full}.json` |
| Third-party model: requirement layer of Airbus's Apollo 11 SysML v2 model read as a circuit through the Pilot syntax tree (56 gates, 95 undriven lines, no shared line, no checkable refinement, no satisfy binding) | `SYSML_KERNEL_DIR=... sh experiments/third_party/apollo11.sh` | `results/reference/third_party/apollo11_requirements_layer.json` |
| Gamma 2.6 + Theta: composed LM machines as a generated Gamma statechart, reachability of the 12 composite states | `python3 baselines/gamma/gamma_baseline.py` (needs Docker and the image `ftsrggamma/headless-gamma`) | `results/reference/gamma/*/gamma_reachability.json`, generated `LMGamma/` project and `LMFSM.xsts` |
| Kind 2 cross-check of the reachable composite states (8 of 12) | `KIND2=... python3 experiments/kind2_reachability.py` | `results/reference/kind2_reach/*/kind2_reachability.json` |
| Figures | `python3 figures/fig_pla.py` etc.; `dot -Tpdf figures/fig_cfg.dot` | — |

Run times depend on the machine. The verdicts, regions and counts do not.

## Repository layout

```
sysmlc/          compiler: parser, semantics (z3), analysis, verilog (Yosys), ic3 (Spacer), views,
                 lustre (Kind 2), diff (miter), bench_scale, logic_engine, pilot_frontend (second front end),
                 unroll (bounded unrolling over time), requirements_layer (requirement layer of any parsed model)
models/          SysML v2 models: Lockheed Martin FSM (original and revised) and FireSat;
                 third_party/: NASA Lift+Cruise requirements generated from FRET (mini and full sets)
case_studies/    scripts over hand-written formulas (FireSat physics, roll autopilot, temporal versions)
baselines/       Kind 2 contracts and driver, OCRA and Gamma generators and drivers, Pacti and flamapy scripts
tests/          translation-fidelity tests (valid, invalid, unsupported, SMT = Verilog = Lustre)
experiments/     defect-injection (mutation) experiment; Kind 2 reachability cross-check; third_party/ (NASA Lift+Cruise, Airbus Apollo 11)
validation/      SysML v2 pilot-implementation syntax check and AST dump (DumpAst.java)
figures/         sources of the figures in the paper
results/reference/  outputs used in the paper
scripts/         run_all.sh, fetch_external.sh
```

## SysML v2 subset and conventions

- **Supported constructs:**
  - `enum def`;
  - `requirement def <'ID'>` with `subject`, `doc`, typed `in`/`out` attributes and `require constraint`;
  - `exhibit state` with `transition t first A if g then B;` (first enabled transition in textual order; none enabled means stay);
  - `variation part def` / `variant part` with `attribute redefines`;
  - `interface def` with `assert constraint`;
  - `action def` with `first/then/decide/fork/merge/join`;
  - `allocate`, and derived attributes in the system part;
  - requirement usages and `#refinement dependency n from c1, c2 to p;` (ModelingMetadata), read as "the sources refine the target";
  - `Integer`, `Real`, `Boolean` and enumeration attributes; attributes of part definitions reached by feature chains.
- **Compiler conventions:**
  - requirements whose ID starts with `GLO` are glossary axioms;
  - `preK_x` is `x` delayed `K` steps, initially false;
  - `fOnBoard` is the allocation indicator of function `f`.
- **Fail-closed front end:**
  - Every statement must match one of the 41 rules of the subset grammar (`GRAMMAR` in `sysmlc/parser.py`), in the context where it appears; an unrecognized statement (for example `garbage blorp;`) is an error. Expression bodies are parsed by a strict expression parser.
  - The compiler rejects, with a diagnostic and exit status 2, any model with a lexical, syntactic, naming or typing error, and any construct outside the subset (for example `assume constraint`, `constraint def`, `calc def`, `accept` triggers, `entry` actions, `flow`, `succession`). Nothing is silently ignored.
  - Every report starts with a translation-coverage line: which constructs were translated, which were read only for structure (`part`, `port`, `connect`, `interface`) and which were rejected.
  - Statements read only for structure (documentation, subjects, imports, parts, ports, interfaces, connections) are not translated. Signals are identified by name, so a connection is not a binding; the compiler checks that ports are typed by declared port definitions, that connections join declared ports of conjugate types, and that every feature chain in an expression starts at a declared port, part usage or subject.
  - Every declared name must be unique in its scope (one namespace per body: package, part, port, state machine, variation, variant, action...), and port names must be unique in the model because signals are resolved by name; at most one part holds `satisfy`/`allocate` relations.
  - `tests/run_tests.py` checks this on 117 cases (see the table above); `.github/workflows/tests.yml` runs it on every push, and the `Dockerfile` gives the same environment locally (`docker build -t sysmlc . && docker run --rm sysmlc`).
  - The cross-check of the SMT, Verilog and Lustre translations is exhaustive for the 20 Boolean/enumerated requirements of the Lockheed Martin model; it is testing, not a proof of the translators, and does not cover real-valued expressions.
  - The guarantee is relative to the subset: `sysmlc` is not a parser for the full SysML v2 grammar. Syntax against the standard is checked separately with the pilot implementation (`validation/`), and the IR built by the grammar is compared with the pilot's syntax tree of every model (`tests/ast_check.py`, test class H). A second front end, `sysmlc/pilot_frontend.py` (`--frontend pilot`), builds the IR from that tree alone; every analysis gives the same results through it (`tests/frontend_check.py`). That comparison covers the models in `models/`; a new model should be dumped and checked the same way.
- **Limitations:**
  - The parser works by pattern matching over this subset, not over the full SysML v2 grammar. The models themselves are valid SysML v2 for the pilot implementation.
  - In the WebAssembly build of Yosys, ABC does not run, so the circuits are optimized with `synth -noabc` + `freduce`.
  - The FireSat parameter values are illustrative.

## Data sources

- **Lockheed Martin cyber-physical challenges**, as formalized by NASA in FRET ([NASA-SW-VnV/fret](https://github.com/NASA-SW-VnV/fret), Apache License 2.0). They are not redistributed here: `scripts/fetch_external.sh` downloads them. The SysML v2 and Lustre models in `models/` and `baselines/kind2/` were written by the authors from the published requirements.
- **NASA Lift+Cruise** requirements, from the same FRET repository (Apache License 2.0). `models/third_party/lpc_{mini,full}.sysml` are generated from them by `experiments/third_party/fret2sysml.py`.
- **Apollo 11 SysML v2 model** by Airbus Central R&T ([airbus/apollo-11-sysml-v2](https://github.com/airbus/apollo-11-sysml-v2), Mozilla Public License 2.0). It is not redistributed here: `experiments/third_party/apollo11.sh` clones the commit analysed.
- **FireSat** top-level requirements and concept options: the public-domain SMAD serialization by capsulecorplab (CC0), after Wertz and Larson, *Space Mission Analysis and Design*, 3rd ed.

## License

- Code: MIT (see `LICENSE`).
- Models and results: CC BY 4.0.

Please cite the article and the Zenodo archive (`CITATION.cff`).
