#!/bin/bash
# Used once, for the restoration patch (gate tp1-p0b). For trees with the `phase-observer` feature use fv_tp1_gate1.sh,
# which also runs the mutant campaign in the deployed configuration.
# Aspis translatability pass: the shared gate (fv_sampler_gate.sh), step for step, with ONE difference: the native
# builds of the CHANGED tree name the verifier crate's own `future-lazy-horner` feature. From the restoration patch
# on, that feature selects the Aspis `semantic_value` and turns on aspis-core's single-reduction multiply-add; the
# shared script names only `aspis-core/future-lazy-horner`, which in a restored tree would compile the pinned
# `semantic_value` natively and leave the deployed one untested. The base tree has no such verifier feature and is
# built with the shared script's lists unchanged. Files written have the names and layout fv_gate_compare.py reads.
# Usage: fv_tp1_gate.sh <name> <tree> <base-tree> <label>=<base ELF>
#   1 integration tests of the verifier crate in the changed tree with the deployed feature set
#   2 fv_round7.sh: SBF build with the deployed features, the recorded payments replayed, the redirect attempts
#   3 the 156,704-mutant campaign built in both trees (each in its own target directory); verdict files compared
#   4 the worst-case tool built in the changed tree, run on the base ELF and the changed ELF
# Time is expected in compilation (the changed tree's four target directories), then about twenty seconds per campaign.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; H=$3; HEADELF=$4
D=$W/GATE_$N.done; rm -f $D
COMMON="optimized-terminal program-build future-validated-decode future-merkle-single-pass future-tight-base future-tight-weights future-lazy-boundary future-d-inactive-tensor future-d-pair-expansion future-merkle-in-place future-fold-shared"
CORE="aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square"
F="prover $COMMON $CORE future-lazy-horner"
FM_BASE="$(for f in $COMMON; do printf 'aspis-r1-cost-probe/%s ' $f; done)$CORE aspis-core/future-lazy-horner"
FM_TREE="$(for f in $COMMON; do printf 'aspis-r1-cost-probe/%s ' $f; done)$CORE aspis-r1-cost-probe/future-lazy-horner"
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
grep -q '^future-lazy-horner' $W/$S/crates/aspis-r1-cost-probe/Cargo.toml || { echo "NO_VERIFIER_LAZY_HORNER_FEATURE in $S" > $D; exit 1; }
bash fv_slot.sh G-$N-tests 1500 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features \"$F\" --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule" || { echo TESTS_FAILED > $D; exit 1; }
bash fv_round7.sh $N $S || { echo ROUND7_FAILED > $D; exit 1; }
TAG=g-$N; M=$W/MUTANTS_$TAG.done; rm -f $M; mkdir -p mutants
mbuild() { # tree, feature list
  cp $W/one_tx_mutants.rs $W/$1/tools/r1-cost-probe/src/bin/one_tx_mutants.rs
  bash fv_slot.sh BM-$TAG-$1 3000 bash -c "cd $W/$1/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-mut-$1 cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$2' && cp $W/target/native-mut-$1/release/one_tx_mutants $W/mutants/one_tx_mutants-$TAG-$1"
}
mbuild $H "$FM_BASE" || { echo BUILD_FAILED_$H > $M; echo MUTANTS_FAILED > $D; exit 1; }
mbuild $S "$FM_TREE" || { echo BUILD_FAILED_$S > $M; echo MUTANTS_FAILED > $D; exit 1; }
for T in $H $S; do
  bash fv_slot.sh MU-$TAG-$T 6000 bash -c "taskset --cpu-list 0-3 $W/mutants/one_tx_mutants-$TAG-$T $W/devnet/PIN2_TRANSACTIONS.json $W/mutants/$TAG-$T.txt 1 4" || { echo RUN_FAILED_$T > $M; echo MUTANTS_FAILED > $D; exit 1; }
done
{
  sha256sum mutants/$TAG-$H.txt mutants/$TAG-$S.txt mutants/one_tx_mutants-$TAG-$H mutants/one_tx_mutants-$TAG-$S one_tx_mutants.rs
  echo "features ($H): $FM_BASE"
  echo "features ($S): $FM_TREE"
  wc -l mutants/$TAG-$H.txt mutants/$TAG-$S.txt
  if cmp -s mutants/$TAG-$H.txt mutants/$TAG-$S.txt; then echo IDENTICAL; else echo "DIFFERENT: $(diff mutants/$TAG-$H.txt mutants/$TAG-$S.txt | grep -c '^<') lines"; diff mutants/$TAG-$H.txt mutants/$TAG-$S.txt | head -20; fi
} > $M 2>&1
grep -q '^IDENTICAL' $M || { echo MUTANTS_FAILED > $D; exit 1; }
B=$W/worst/one_tx_worst-$N-$S
cp $W/one_tx_worst.rs $W/$S/tools/r1-cost-probe/src/bin/one_tx_worst.rs
bash fv_slot.sh G-$N-wbuild 3000 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$S/release/one_tx_worst $B" || { echo WORST_BUILD_FAILED > $D; exit 1; }
SPECS=withdrawal:255:60:full,withdrawal:255:1:full,withdrawal:1023:1:full,withdrawal:254:1:full,withdrawal:0:1:genesis,transfer:255:1:full
bash fv_slot.sh G-$N-wrun 3000 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/worst/gate-$N.json '$SPECS' $HEADELF $N=$W/out/$N/artifacts/aspis_r1_cost_probe_program.so" || { echo WORST_RUN_FAILED > $D; exit 1; }
{ echo OK; cat $M | head -9; cat $W/ROUND7_$N.done; sha256sum $W/out/$N/artifacts/aspis_r1_cost_probe_program.so $W/worst/gate-$N.json $B; } > $D 2>&1
