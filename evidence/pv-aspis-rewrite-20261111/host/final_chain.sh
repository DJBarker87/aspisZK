#!/bin/bash
# Final chain. (1) The two baseline test suites that had not compiled for want of input files (prover, probe), on
# a separate copy of the base tree (src-base, own cargo target directory). (2) Gates A, B, C and all test suites
# once more on the final rewritten tree (tag final), through after_chain.sh.
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111; cd $W; J="bash $W/tools/job.sh"
for s in prover probe; do
  PV_SRC_DIR=src-base $J T-base3-$s 5400 "cargo test --release, suite $s, base revision (src-base); time expected in compilation then tests" bash $W/tools/tests.sh base3 $s
done
bash $W/tools/after_chain.sh final "$1"
echo done > $W/FINAL_CHAIN.DONE
