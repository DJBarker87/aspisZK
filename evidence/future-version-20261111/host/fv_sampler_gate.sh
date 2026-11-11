#!/bin/bash
# Gates for a verifier-shared source change (first use: the index-loop rewrite of
# sampler::low_base_p_digits). Compares a changed source tree with the head's tree.
# Usage: fv_sampler_gate.sh <name> <changed-tree> <head-tree> <head-elf-label=path>
#   1 integration tests of the changed tree with the deployed feature set
#   2 SBF build of the changed tree, replay of the two recorded payments, redirect attempts
#   3 mutation campaign: verdict files of the two trees must be identical
#   4 worst-case tool BUILT IN THE CHANGED TREE (so the prover and the re-pack use the changed
#     code): fixture proofs for chosen scenarios; their pinned and re-packed proof hashes are
#     compared by the caller with those of the tool built in the unchanged tree (prover byte
#     identity), and the compute of the changed ELF is measured beside the head's ELF.
# Time is expected in compilation (three cold builds of the changed tree), then seconds per run
# and a few seconds per fixture proof. Each tree has its own cargo target directories.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; H=$3; HEADELF=$4
D=$W/GATE_$N.done; rm -f $D
F="prover optimized-terminal program-build future-validated-decode future-merkle-single-pass future-tight-base future-tight-weights future-lazy-boundary future-d-inactive-tensor future-d-pair-expansion future-merkle-in-place future-fold-shared aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square aspis-core/future-lazy-horner"
FM="aspis-r1-cost-probe/optimized-terminal aspis-r1-cost-probe/program-build aspis-r1-cost-probe/future-validated-decode aspis-r1-cost-probe/future-merkle-single-pass aspis-r1-cost-probe/future-tight-base aspis-r1-cost-probe/future-tight-weights aspis-r1-cost-probe/future-lazy-boundary aspis-r1-cost-probe/future-d-inactive-tensor aspis-r1-cost-probe/future-d-pair-expansion aspis-r1-cost-probe/future-merkle-in-place aspis-r1-cost-probe/future-fold-shared aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square aspis-core/future-lazy-horner"
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
bash fv_slot.sh G-$N-tests 1500 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features \"$F\" --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule" || { echo TESTS_FAILED > $D; exit 1; }
bash fv_round7.sh $N $S || { echo ROUND7_FAILED > $D; exit 1; }
bash fv_mutants.sh g-$N 1 $H $S "$FM" || { echo MUTANTS_FAILED > $D; exit 1; }
B=$W/worst/one_tx_worst-$S
if [ ! -x $B ]; then
  cp $W/one_tx_worst.rs $W/$S/tools/r1-cost-probe/src/bin/one_tx_worst.rs
  bash fv_slot.sh G-$N-wbuild 3000 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$S/release/one_tx_worst $B" || { echo WORST_BUILD_FAILED > $D; exit 1; }
fi
SPECS=withdrawal:255:60:full,withdrawal:255:1:full,withdrawal:1023:1:full,withdrawal:254:1:full,withdrawal:0:1:genesis,transfer:255:1:full
bash fv_slot.sh G-$N-wrun 3000 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/worst/gate-$N.json '$SPECS' $HEADELF $N=$W/out/$N/artifacts/aspis_r1_cost_probe_program.so" || { echo WORST_RUN_FAILED > $D; exit 1; }
{ echo OK; cat $W/MUTANTS_g-$N.done | head -9; cat $W/ROUND7_$N.done; sha256sum $W/out/$N/artifacts/aspis_r1_cost_probe_program.so $W/worst/gate-$N.json $B; } > $D 2>&1
