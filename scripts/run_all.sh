#!/bin/sh
# Reproduce every result of the paper. Outputs go to results/out/. Reference outputs are in results/reference/.
# Optional tools: KIND2 (path to the Kind 2 binary, v2.2.0), Z3_BIN (z3 executable used by Kind 2),
# SYSML_KERNEL_DIR (SysML v2 pilot implementation, for the syntax check).
set -e
ROOT=$(cd "$(dirname "$0")/.." && pwd); cd "$ROOT"
O=$ROOT/results/out; mkdir -p $O/case_studies $O/kind2 $O/pacti $O/flamapy
echo "[0] Translation-fidelity tests (Section V): 68 tests, classes A-G"
python3 tests/run_tests.py
echo "[1] Compiler: Lockheed Martin and FireSat models (Sections VI, Table 3, Figs. 2, 4, 5)"
python3 sysmlc/__main__.py models/lmcps_fsm.sysml -o $O/lmcps
python3 sysmlc/__main__.py models/firesat.sysml   -o $O/firesat
echo "[2] Semantic difference between requirement versions (Section VII-A)"
python3 sysmlc/diff.py models/lmcps_fsm.sysml models/lmcps_fsm_rev.sysml -o $O/diff
echo "[3] Case studies on hand-written formulas (FireSat flow-down, roll autopilot, holes, temporal versions)"
[ -d external/fret ] || sh scripts/fetch_external.sh
for s in case_firesat2 case_lmcps_roll case_lmcps_fsm case_lmcps_fsm_temporal case_lmcps_fsm_holes; do
  OUT=$O/case_studies python3 case_studies/$s.py > $O/case_studies/$s.log
done
echo "[4] Scalability sweep (Fig. 6) - takes about 10 min"
OUT=$O python3 sysmlc/bench_scale.py > $O/bench_scale.log
echo "[5] Baselines (Section VII-A, Table 4)"
if command -v "${KIND2:-kind2}" >/dev/null 2>&1; then
  (cd baselines/kind2 && python3 iterate.py > /dev/null && mv kind2_results.json $O/kind2/ && rm -f tmp.lus)
  python3 sysmlc/lustre.py models/lmcps_fsm.sysml $O/kind2/design
else echo "  Kind 2 not found: set KIND2 to run the realizability and model-checking baselines"; fi
(cd baselines/pacti && python3 firesat_pacti.py > /dev/null && mv pacti_results.json $O/pacti/)
(cd baselines/flamapy && python3 -W ignore fm.py > /dev/null && mv flamapy_results.json *.uvl $O/flamapy/)
echo "[5b] Defect-injection (mutation) experiment: 90 mutants, miter vs IC3/PDR vs Kind 2 (Section VII-B, Table 5)"
if command -v "${KIND2:-kind2}" >/dev/null 2>&1; then OUT=$O python3 experiments/mutation.py > $O/mutation.log
else echo "  Kind 2 not found: set KIND2 to run the mutation experiment"; fi
echo "[6] Figures"
mkdir -p $O/figures; (cd $O/figures && for f in fig_pla fig_act fig_scale; do python3 $ROOT/figures/$f.py; done \
  && dot -Tpdf $ROOT/figures/fig_cfg.dot -o fig_cfg.pdf && dot -Tpdf $ROOT/figures/fig_arch.dot -o fig_arch.pdf)
echo "[7] SysML v2 syntax check"
if [ -n "$SYSML_KERNEL_DIR" ]; then sh validation/validate.sh; else echo "  set SYSML_KERNEL_DIR to run it"; fi
echo "Done. Compare results/out with results/reference."
