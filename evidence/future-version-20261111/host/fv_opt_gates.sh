#!/bin/bash
# Optimisation rounds: equivalence gates for one candidate tree src-opt-<name>.
# Usage: fv_opt_gates.sh <name>
# 1. the mutation campaign (one_tx_mutants, deployed feature set, own target directory
#    target/native-mut-<tree>), verdict file compared byte for byte with X1's (mutants/dep2-src-xp1.txt,
#    reused, not rerun);
# 2. the statement-binding and equivalence tests with the deployed feature set (own target directory
#    target/native-test-<tree>), and the fused-verifier library tests (kernel equivalence, the six
#    fixtures, every-region mutations, slot bounds).
# Time is expected in compilation (two cold native builds of a few minutes); the campaign runs in
# seconds.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; T=src-opt-$N
D=$W/OPT_GATES_$N.done; rm -f $D
FEAT_MUT='aspis-r1-cost-probe/optimized-terminal aspis-r1-cost-probe/program-build aspis-r1-cost-probe/future-validated-decode aspis-r1-cost-probe/future-merkle-single-pass aspis-r1-cost-probe/future-tight-base aspis-r1-cost-probe/future-tight-weights aspis-r1-cost-probe/future-lazy-boundary aspis-r1-cost-probe/future-d-inactive-tensor aspis-r1-cost-probe/future-d-pair-expansion aspis-r1-cost-probe/future-merkle-in-place aspis-r1-cost-probe/future-fold-shared aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square aspis-core/future-lazy-horner'
FEAT_TEST='prover optimized-terminal program-build future-validated-decode future-merkle-single-pass future-tight-base future-tight-weights future-lazy-boundary future-d-inactive-tensor future-d-pair-expansion future-merkle-in-place future-fold-shared aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square aspis-core/future-lazy-horner'
ENVC="env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
mkdir -p mutants
cmp -s one_tx_mutants.rs $T/tools/r1-cost-probe/src/bin/one_tx_mutants.rs || cp one_tx_mutants.rs $T/tools/r1-cost-probe/src/bin/one_tx_mutants.rs
B=$W/mutants/one_tx_mutants-opt-$T
if [ ! -x $B ]; then
  bash fv_slot.sh OPT-BM-$N 3000 bash -c "cd $W/$T/tools/r1-cost-probe && taskset --cpu-list 0-3 $ENVC CARGO_TARGET_DIR=$W/target/native-mut-$T cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$FEAT_MUT' && cp $W/target/native-mut-$T/release/one_tx_mutants $B" || { echo "MUTANTS_BUILD_FAILED" >> $D; exit 1; }
fi
bash fv_slot.sh OPT-MU-$N 6000 bash -c "taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/mutants/opt-$T.txt 1 4" || { echo "MUTANTS_RUN_FAILED" >> $D; exit 1; }
{
  sha256sum mutants/dep2-src-xp1.txt mutants/opt-$T.txt $B one_tx_mutants.rs
  wc -l mutants/dep2-src-xp1.txt mutants/opt-$T.txt
  if cmp -s mutants/dep2-src-xp1.txt mutants/opt-$T.txt; then echo "MUTANTS IDENTICAL"; else echo "MUTANTS DIFFERENT: $(diff mutants/dep2-src-xp1.txt mutants/opt-$T.txt | grep -c '^<') lines"; diff mutants/dep2-src-xp1.txt mutants/opt-$T.txt | head -20; fi
} >> $D 2>&1
bash fv_slot.sh OPT-T-$N 3000 bash -c "cd $W/$T && taskset --cpu-list 0-3 $ENVC CARGO_TARGET_DIR=$W/target/native-test-$T cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features '$FEAT_TEST' --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix"
echo "tests exit $? ($(grep -h '^test result' receipts/OPT-T-$N/stdout.log | awk '{s+=$4; f+=$6} END {print s" passed, "f" failed"}'))" >> $D
bash fv_slot.sh OPT-TL-$N 3000 bash -c "cd $W/$T && taskset --cpu-list 0-3 $ENVC CARGO_TARGET_DIR=$W/target/native-test-$T cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features '$FEAT_TEST' --lib -- fused:: multiproof::"
echo "library tests exit $? ($(grep -h '^test result' receipts/OPT-TL-$N/stdout.log | awk '{s+=$4; f+=$6} END {print s" passed, "f" failed"}'))" >> $D
echo DONE >> $D
