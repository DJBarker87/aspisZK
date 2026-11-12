#!/bin/bash
# Baseline chain at the base revision (one scope at a time).
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
cd $W; J="bash $W/tools/job.sh"
$J B-base-sbf 5400 "SBF builds of the six program targets at the base revision; time expected in compilation" bash $W/tools/sbf_all.sh base
$J B-base-native 3600 "optimized build of pv_bytes_gate at the base revision; time expected in compilation" bash $W/tools/native_build.sh base
$J G-base-table-1 3600 "gate B table at the base revision, seeds 1..24; time expected in proof generation (release binary)" bash $W/tools/table.sh base 1 1 24
for s in core statement prover probe tool; do
  $J T-base-$s 5400 "cargo test --release, suite $s, base revision; time expected in compilation then tests" bash $W/tools/tests.sh base $s
done
echo done > $W/BASE_CHAIN_DONE
