#!/bin/bash
# Aspis translatability pass (verifier crate and program adapter): everything one batch of rewrites must pass.
# SUPERSEDED by fv_tp1_gate1.sh (the same steps in one fv_slot.sh scope, and the mutant campaign in both the observed
# and the deployed configuration). This script was never run to completion; it is kept because an earlier report named it.
# Usage: fv_tp1_batch.sh <gate-name> <tree> <base-tree> <base-label>=<base ELF> <base-label>
#   1 unit tests of the verifier crate in the changed tree with the deployed feature set (the differential oracles
#     kept beside the rewritten functions), release build
#   2 client configuration: the crate built with r1p-check (prover on, no future-* feature), and its unit tests
#     whose name contains "prover" or "sim"
#   3 fv_tp1_gate.sh, the shared gate fv_sampler_gate.sh step for step with the verifier crate's own
#     future-lazy-horner feature named for the changed tree (integration tests, SBF build, replays, redirect attempts, mutant verdict
#     comparison with the base tree, worst-case tool built in the changed tree)
#   4 fv_gate_compare.py: one verdict per gate
# Time is expected in compilation (cold target directories of the changed tree), then the mutant campaign.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; H=$3; HEADELF=$4; LABEL=$5
D=$W/TP1_BATCH_$N.done; : > $D
F="prover optimized-terminal program-build future-validated-decode future-merkle-single-pass future-tight-base future-tight-weights future-lazy-boundary future-d-inactive-tensor future-d-pair-expansion future-merkle-in-place future-fold-shared aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square future-lazy-horner"
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
bash fv_slot.sh TP-U-$N 2400 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features \"$F\" --lib 2>&1 | grep -E '^test |test result|^error|panicked' | tail -150"; echo "unit tests (deployed features) exit $?" >> $D
grep -E "test result" $W/receipts/TP-U-$N/stdout.log >> $D
bash fv_slot.sh TP-K-$N 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-client-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features r1p-check --lib -- prover sim 2>&1 | grep -E '^test |test result|^error|panicked|warning: unused' | tail -80"; echo "client configuration (r1p-check) build and prover/sim unit tests exit $?" >> $D
grep -E "test result" $W/receipts/TP-K-$N/stdout.log >> $D
bash fv_tp1_gate.sh $N $S $H $HEADELF >> $W/tp1/gate-$N.log 2>&1; echo "gate script (fv_tp1_gate.sh) exit $?" >> $D
python3 fv_gate_compare.py $N $LABEL >> $D 2>&1; echo "gate compare exit $?" >> $D
echo DONE >> $D
