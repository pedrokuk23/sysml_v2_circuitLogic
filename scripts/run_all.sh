#!/bin/sh
# Reproduce every result of the paper. Outputs go to results/out/. Reference outputs are in results/reference/.
# Optional tools: KIND2 (path to the Kind 2 binary, v2.2.0), Z3_BIN (z3 executable used by Kind 2),
# SYSML_KERNEL_DIR (SysML v2 pilot implementation, for the syntax check).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT"
O=$ROOT/results/out; mkdir -p $O/case_studies $O/kind2 $O/pacti $O/flamapy
echo "[0] Translation-fidelity tests: 96 tests, classes A-H"
python3 tests/run_tests.py
echo "[1] Compiler: Lockheed Martin and FireSat models"
python3 sysmlc/__main__.py models/lmcps_fsm.sysml -o $O/lmcps
python3 sysmlc/__main__.py models/firesat.sysml   -o $O/firesat
python3 sysmlc/__main__.py models/firesat_flowdown.sysml -o $O/firesat_flowdown --no-eda   # about 1.5 min
python3 sysmlc/__main__.py models/lmcps_roll_tsm.sysml -o $O/lmcps_roll_tsm --no-eda
python3 sysmlc/__main__.py models/lmcps_roll_tsm_glossary.sysml -o $O/lmcps_roll_tsm_glossary --no-eda
echo "[2] Semantic difference between requirement versions"
python3 sysmlc/diff.py models/lmcps_fsm.sysml models/lmcps_fsm_rev.sysml -o $O/diff
echo "[3] Independent cross-checks on hand-written formulas (same results as the compiler), holes, temporal versions"
[ -d external/fret ] || sh scripts/fetch_external.sh
for s in case_firesat2 case_lmcps_roll case_lmcps_fsm case_lmcps_fsm_temporal case_lmcps_fsm_holes; do
  OUT=$O/case_studies python3 case_studies/$s.py > $O/case_studies/$s.log
done
echo "[4] Scalability sweep - takes about 10 min"
OUT=$O python3 sysmlc/bench_scale.py > $O/bench_scale.log
echo "[5] Baselines"
if command -v "${KIND2:-kind2}" >/dev/null 2>&1; then
  (cd baselines/kind2 && python3 iterate.py > /dev/null && mv kind2_results.json $O/kind2/ && rm -f tmp.lus)
  python3 sysmlc/lustre.py models/lmcps_fsm.sysml $O/kind2/design
  python3 experiments/kind2_reachability.py $O/kind2_reach
else echo "  Kind 2 not found: set KIND2 to run the realizability and model-checking baselines"; fi
if [ -n "$OCRA" ]; then python3 baselines/ocra/ocra_baseline.py $O/ocra > /dev/null; else echo "  set OCRA to run the OCRA baseline"; fi
if command -v docker >/dev/null 2>&1 && docker image inspect ftsrggamma/headless-gamma >/dev/null 2>&1; then python3 baselines/gamma/gamma_baseline.py $O/gamma; else echo "  Docker image ftsrggamma/headless-gamma not found: skipping the Gamma baseline"; fi
python3 experiments/forced_conflicts.py models/lmcps_fsm.sysml $O/case_studies/forced_conflicts.json > /dev/null
F=external/fret/caseStudies/LiftPlusCruise
for s in mini full; do
  python3 experiments/third_party/validate_translation.py $F/LPC_${s}_reqts_and_vars.json models/third_party/lpc_$s.sysml 20 \
    $O/translation_validation_$s.json
done
python3 experiments/third_party/lpc.py $O/lpc_results.json > /dev/null
if [ -n "$SYSML_KERNEL_DIR" ]; then sh experiments/third_party/apollo11.sh $O; fi
(cd baselines/pacti && python3 firesat_pacti.py > /dev/null && mv pacti_results.json $O/pacti/)
(cd baselines/flamapy && python3 -W ignore fm.py > /dev/null && mv flamapy_results.json *.uvl $O/flamapy/)
echo "[5b] Defect-injection (mutation) experiment on the original and the revised set: miter vs IC3/PDR vs Kind 2"
if command -v "${KIND2:-kind2}" >/dev/null 2>&1; then OUT=$O python3 experiments/mutation.py > $O/mutation.log
  python3 experiments/mutation.py --model models/lmcps_fsm_rev.sysml -o $O/mutation_rev > $O/mutation_rev.log
  python3 experiments/mutation_regions.py --json $O/mutation/mutation.json > $O/mutation_regions.log
  python3 experiments/mutation_regions.py --model models/lmcps_fsm_rev.sysml --json $O/mutation_rev/mutation.json >> $O/mutation_regions.log
else echo "  Kind 2 not found: set KIND2 to run the mutation experiment"; fi
echo "[6] Figures"
mkdir -p $O/figures; (cd $O/figures && for f in fig_pla fig_act fig_scale; do python3 $ROOT/figures/$f.py; done \
  && dot -Tpdf $ROOT/figures/fig_cfg.dot -o fig_cfg.pdf && dot -Tpdf $ROOT/figures/fig_arch.dot -o fig_arch.pdf)
echo "[7] SysML v2 syntax check"
if [ -n "$SYSML_KERNEL_DIR" ]; then sh validation/validate.sh; sh validation/dump_ast.sh; python3 tests/ast_check.py; else echo "  set SYSML_KERNEL_DIR to run it"; fi
echo "Done. Compare results/out with results/reference."
