# sysmlc — Systems Models as Logic Circuits

Code, models and data for the article

> P. Kukulka de Albuquerque, "Systems Models as Logic Circuits: Compiling SysML v2 Requirements, Behavior,
> Variability and Allocation Into Digital Logic," manuscript in preparation for *IEEE Access*, 2026.

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
  - [Kind 2](https://github.com/kind2-mc/kind2/releases) v2.2.0, with `KIND2=/path/to/kind2` (and `Z3_BIN=/path/to/z3` if needed);
  - Java 17 and the SysML v2 Pilot Implementation 0.63.1, for the syntax check (`SYSML_KERNEL_DIR`, see `validation/`).

## Reproducing the paper

```
sh scripts/run_all.sh        # about 15 min; outputs in results/out/, reference outputs in results/reference/
```

Or step by step:

| Paper item | Command | Reference output |
|---|---|---|
| Lockheed Martin model: conflicts C1–C5, holes 24 + 14, port contract, proofs (Table 3), IC3/PDR invariant, AIG sizes (Section VI-A, Fig. 2) | `python3 sysmlc/__main__.py models/lmcps_fsm.sysml -o results/out/lmcps` | `results/reference/lmcps/REPORT.md`, `results.json`, `design.sv`, `reqs.v` |
| FireSat: 9 of 32 configurations, dead `geo1`, core `leo2`, allocation, action flow (Section VI-B, Figs. 4–5) | `python3 sysmlc/__main__.py models/firesat.sysml -o results/out/firesat` | `results/reference/firesat/` |
| Semantic difference between the original and revised requirements (Section VII-A) | `python3 sysmlc/diff.py models/lmcps_fsm.sysml models/lmcps_fsm_rev.sysml -o results/out/diff` | `results/reference/diff/diff.json` |
| Scalability sweep (Fig. 6) | `OUT=results/out python3 sysmlc/bench_scale.py` | `results/reference/bench_scale.json` |
| FireSat quantitative flow-down: abduction, interpolants and margin, discretization, geostationary case (Section VI-B) | `OUT=results/out python3 case_studies/case_firesat2.py` | `results/reference/case_studies/case_firesat2.json` |
| Roll autopilot AP-003A–D: vacuous clause, conflict regions, triplex monitor | `OUT=results/out python3 case_studies/case_lmcps_roll.py` | `case_lmcps_roll.json` |
| FSM-001 temporal versions; hypotheses of the proof; 5 of 34 holds | `OUT=results/out python3 case_studies/case_lmcps_fsm_temporal.py`, then `case_lmcps_fsm_holes.py` | `case_lmcps_fsm_temporal.json`, `case_lmcps_fsm_holes.json` |
| Original FRET requirement set (needs `sh scripts/fetch_external.sh`) | `OUT=results/out python3 case_studies/case_lmcps_fsm.py` | `case_lmcps_fsm.json` |
| Translation-fidelity tests: 68 tests in seven classes, including an unknown statement inserted at all 514 statement boundaries, changes to structure-only statements and a copy of each of the 483 declarations (Section V) | `python3 tests/run_tests.py` | `tests/test_results.json` |
| Defect injection: 90 mutants of FSM-002–013; miter vs IC3/PDR vs Kind 2 (Section VII-B, Table 5) | `KIND2=... OUT=results/out python3 experiments/mutation.py` | `results/reference/mutation/mutation.json` |
| Kind 2 realizability, the FRET back end (Section VII-A, Table 4) | `cd baselines/kind2 && python3 iterate.py` | `results/reference/kind2/kind2_results.json` |
| Kind 2 model checking of the compiled design (Table 4) | `python3 sysmlc/lustre.py models/lmcps_fsm.sysml results/out/kind2` | `results/reference/kind2/kind2.json`, `design.lus` |
| Pacti contract quotient (Table 4) | `cd baselines/pacti && python3 firesat_pacti.py` | `results/reference/pacti/pacti_results.json` |
| flamapy feature-model analysis (Table 4) | `cd baselines/flamapy && python3 fm.py` | `results/reference/flamapy/` |
| SysML v2 syntax check (0 errors, 0 warnings) | `SYSML_KERNEL_DIR=... sh validation/validate.sh` | `validation/validation_0.63.1.log` |
| Figures 1, 2, 4, 5, 6 | `python3 figures/fig_pla.py` etc.; `dot -Tpdf figures/fig_cfg.dot` | — |

Run times depend on the machine. The verdicts, regions and counts do not.

## Repository layout

```
sysmlc/          compiler: parser, semantics (z3), analysis, verilog (Yosys), ic3 (Spacer), views,
                 lustre (Kind 2), diff (miter), bench_scale, logic_engine
models/          SysML v2 models: Lockheed Martin FSM (original and revised) and FireSat
case_studies/    scripts over hand-written formulas (FireSat physics, roll autopilot, temporal versions)
baselines/       Kind 2 contracts and driver, Pacti and flamapy scripts
tests/          translation-fidelity tests (valid, invalid, unsupported, SMT = Verilog = Lustre)
experiments/     defect-injection (mutation) experiment
validation/      SysML v2 pilot-implementation syntax check
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
  - `allocate`, and derived attributes in the system part.
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
  - `tests/run_tests.py` checks this on 68 cases (see the table above); `.github/workflows/tests.yml` runs it on every push, and the `Dockerfile` gives the same environment locally (`docker build -t sysmlc . && docker run --rm sysmlc`).
  - The cross-check of the SMT, Verilog and Lustre translations is exhaustive for the 20 Boolean/enumerated requirements of the Lockheed Martin model; it is testing, not a proof of the translators, and does not cover real-valued expressions.
  - The guarantee is relative to the subset: `sysmlc` is not a parser for the full SysML v2 grammar. Syntax against the standard is checked separately with the pilot implementation (`validation/`).
- **Limitations:**
  - The parser works by pattern matching over this subset, not over the full SysML v2 grammar. The models themselves are valid SysML v2 for the pilot implementation.
  - In the WebAssembly build of Yosys, ABC does not run, so the circuits are optimized with `synth -noabc` + `freduce`.
  - The FireSat parameter values are illustrative.

## Data sources

- **Lockheed Martin cyber-physical challenges**, as formalized by NASA in FRET ([NASA-SW-VnV/fret](https://github.com/NASA-SW-VnV/fret), NASA Open Source Agreement). They are not redistributed here: `scripts/fetch_external.sh` downloads them. The SysML v2 and Lustre models in `models/` and `baselines/kind2/` were written by the author from the published requirements.
- **FireSat** top-level requirements and concept options: the public-domain SMAD serialization by capsulecorplab (CC0), after Wertz and Larson, *Space Mission Analysis and Design*, 3rd ed.

## License

- Code: MIT (see `LICENSE`).
- Models and results: CC BY 4.0.

Please cite the article and the Zenodo archive (`CITATION.cff`).
