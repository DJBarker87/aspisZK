#!/bin/bash
# Runs INSIDE one fv_slot.sh scope (started by fv_tp1_gate1.sh). See that file.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; H=$3; HEADELF=$4
D=$W/GATE_$N.done; ST=$W/tp1/gate1-$N.steps; : > $ST; LOGS=$W/tp1/gate1-$N; mkdir -p $LOGS
COMMON="optimized-terminal program-build future-validated-decode future-merkle-single-pass future-tight-base future-tight-weights future-lazy-boundary future-d-inactive-tensor future-d-pair-expansion future-merkle-in-place future-fold-shared"
CORE="aspis-core/future-fast-kmul aspis-core/future-fast-prepared aspis-core/future-fast-square"
F="prover $COMMON $CORE future-lazy-horner"
FM_BASE="$(for f in $COMMON; do printf 'aspis-r1-cost-probe/%s ' $f; done)$CORE aspis-core/future-lazy-horner"
FM_TREE="$(for f in $COMMON; do printf 'aspis-r1-cost-probe/%s ' $f; done)$CORE aspis-r1-cost-probe/future-lazy-horner"
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
E=$W/out/$N/artifacts/aspis_r1_cost_probe_program.so
bad=0
step() { # name, command...
  local name=$1; shift; local t0=$(date +%s)
  "$@" > $LOGS/$name.log 2>&1; local rc=$?
  echo "$name exit $rc; wall $(( $(date +%s) - t0 )) s" >> $ST
  return $rc
}
grep -q '^future-lazy-horner' $W/$S/crates/aspis-r1-cost-probe/Cargo.toml || { echo "NO_VERIFIER_LAZY_HORNER_FEATURE in $S" > $D; exit 1; }
# 1 unit tests of the verifier crate with the deployed feature set (the differential oracles beside the rewrites)
step unit-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features \"$F\" --lib" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/unit-tests.log | head -20 >> $ST
# 2 client configuration: r1p-check (prover on, no future-* feature), unit tests whose name contains prover or sim
step client-config bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-client-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features r1p-check --lib -- prover sim" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/client-config.log | head -20 >> $ST
# 2b unit tests of the PROGRAM crate (the adapter), native, deployed features, in the changed tree and in the base tree
#    (each in its own target directory; the base tree is only read). The two result lines must agree.
step program-tests-$S bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features $K --lib"
step program-tests-$H bash -c "cd $W/$H && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$H cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features $K --lib"
PT1=$(grep -E "^test result" $LOGS/program-tests-$S.log | sed -E 's/; finished in .*//' | tr '\n' ' '); PT0=$(grep -E "^test result" $LOGS/program-tests-$H.log | sed -E 's/; finished in .*//' | tr '\n' ' ')
echo "program crate tests, changed tree: ${PT1:-no result line}" >> $ST; echo "program crate tests, base tree:    ${PT0:-no result line}" >> $ST
if [ "$PT1" != "$PT0" ] || echo "$PT1" | grep -q FAILED; then bad=1; echo "program crate tests DIFFER from the base tree or fail" >> $ST; fi
# 3 the shared gate's integration tests
step integration-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features \"$F\" --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule" || { bad=1; echo TESTS_FAILED > $D; }
grep -E "test result|FAILED|panicked" $LOGS/integration-tests.log | head -20 >> $ST
# 4 fv_round7.sh: SBF build with the deployed features, the two recorded payments replayed, the redirect attempts
R7=$W/ROUND7_$N.done
step sbf-build bash $W/fv_build_adapter_src.sh $N $K $S || { echo BUILD_FAILED > $R7; echo ROUND7_FAILED > $D; exit 1; }
mkdir -p replays-v5 replays-redirect
for op in transfer withdrawal; do
  step replay-$op bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $E $op $W/replays-v5/$N-$op.json" || { echo REPLAY_FAILED_$op > $R7; echo ROUND7_FAILED > $D; exit 1; }
done
step redirect bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $E $W/replays-redirect/$N-withdrawal.json"; echo "redirect exit $?" > $R7
cp $W/target/sbf-adapter-$S/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so $LOGS/unstripped-$S.so 2>/dev/null
# 5 the mutant campaign (156,704 mutants of the two recorded proofs), built in both trees, own target directory each.
#   The tool passes an observer and prints, per mutant, the verdict and the number of observer marks reached.
#   A tree whose verifier crate has the `phase-observer` feature carries the observer only with that feature, and the
#   deployed program is built without it. Such a tree is therefore run twice:
#     observed  (deployed features + phase-observer): the verdict file must be byte-identical to the base tree's;
#     deployed  (deployed features only, the observer is dropped): every mark count must be 0 and the verdicts
#               (the file without its last column) must be identical to the base tree's verdicts.
#   The second run is the one that executes the functions the deployed program executes.
TAG=g-$N; M=$W/MUTANTS_$TAG.done; mkdir -p mutants
HOOK=0; grep -q '^phase-observer' $W/$S/crates/aspis-r1-cost-probe/Cargo.toml && HOOK=1
mbuild() { # tree, feature list, binary suffix; the base tree is never written: its copy of the tool source must already be the shared one
  if [ $1 = $H ]; then cmp -s $W/one_tx_mutants.rs $W/$1/tools/r1-cost-probe/src/bin/one_tx_mutants.rs || { echo "base tree $1 lacks the shared one_tx_mutants.rs" >> $ST; return 1; }
  else cmp -s $W/one_tx_mutants.rs $W/$1/tools/r1-cost-probe/src/bin/one_tx_mutants.rs || cp $W/one_tx_mutants.rs $W/$1/tools/r1-cost-probe/src/bin/one_tx_mutants.rs; fi
  step mutant-build-$1$3 bash -c "cd $W/$1/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-mut-$1 cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$2' && cp $W/target/native-mut-$1/release/one_tx_mutants $W/mutants/one_tx_mutants-$TAG-$1$3"; }
mrun() { step mutant-run-$1 bash -c "taskset --cpu-list 0-3 $W/mutants/one_tx_mutants-$TAG-$1 $W/devnet/PIN2_TRANSACTIONS.json $W/mutants/$TAG-$1.txt 1 4"; }
mok=1
mbuild $H "$FM_BASE" "" && mrun $H || { echo BUILD_OR_RUN_FAILED_$H > $M; mok=0; }
if [ $mok = 1 ] && [ $HOOK = 1 ]; then
  mbuild $S "$FM_TREE aspis-r1-cost-probe/phase-observer" "" && mrun $S || { echo BUILD_OR_RUN_FAILED_$S > $M; mok=0; }
  [ $mok = 1 ] && { mbuild $S "$FM_TREE" "-deployed" && mrun $S-deployed || { echo BUILD_OR_RUN_FAILED_$S-deployed > $M; mok=0; }; }
elif [ $mok = 1 ]; then
  mbuild $S "$FM_TREE" "" && mrun $S || { echo BUILD_OR_RUN_FAILED_$S > $M; mok=0; }
fi
if [ $mok = 1 ]; then
  {
    sha256sum mutants/$TAG-$H.txt mutants/$TAG-$S.txt mutants/one_tx_mutants-$TAG-$H mutants/one_tx_mutants-$TAG-$S one_tx_mutants.rs
    echo "features ($H): $FM_BASE"
    echo "features ($S): $FM_TREE$([ $HOOK = 1 ] && echo ' aspis-r1-cost-probe/phase-observer')"
    wc -l mutants/$TAG-$H.txt mutants/$TAG-$S.txt
    same=1
    cmp -s mutants/$TAG-$H.txt mutants/$TAG-$S.txt || { same=0; echo "observed run DIFFERENT: $(diff mutants/$TAG-$H.txt mutants/$TAG-$S.txt | grep -c '^<') lines"; diff mutants/$TAG-$H.txt mutants/$TAG-$S.txt | head -20; }
    if [ $HOOK = 1 ]; then
      sha256sum mutants/$TAG-$S-deployed.txt mutants/one_tx_mutants-$TAG-$S-deployed
      echo "features ($S, deployed run): $FM_TREE"
      strip() { awk '/^#/ {print; next} {NF=NF-1; print}' "$1"; }
      strip mutants/$TAG-$H.txt > mutants/$TAG-$H.verdicts.txt; strip mutants/$TAG-$S-deployed.txt > mutants/$TAG-$S-deployed.verdicts.txt
      sha256sum mutants/$TAG-$H.verdicts.txt mutants/$TAG-$S-deployed.verdicts.txt
      nz=$(awk '!/^#/ && $NF != 0' mutants/$TAG-$S-deployed.txt | wc -l)
      echo "deployed run: lines with a nonzero mark count: $nz (must be 0)"
      [ "$nz" = 0 ] || same=0
      cmp -s mutants/$TAG-$H.verdicts.txt mutants/$TAG-$S-deployed.verdicts.txt || { same=0; echo "deployed run verdicts DIFFERENT: $(diff mutants/$TAG-$H.verdicts.txt mutants/$TAG-$S-deployed.verdicts.txt | grep -c '^<') lines"; diff mutants/$TAG-$H.verdicts.txt mutants/$TAG-$S-deployed.verdicts.txt | head -20; }
    fi
    [ $same = 1 ] && echo IDENTICAL
  } > $M 2>&1
  grep -q '^IDENTICAL' $M || { mok=0; }
fi
[ $mok = 1 ] || { bad=1; echo MUTANTS_FAILED > $D; }
echo "mutants: $(grep -E '^IDENTICAL|DIFFERENT|FAILED|must be 0' $M | tr '\n' ';' | cut -c1-300)" >> $ST
# 6 the worst-case tool built in the changed tree, run on the base ELF and the changed ELF
B=$W/worst/one_tx_worst-$N-$S
cp $W/one_tx_worst.rs $W/$S/tools/r1-cost-probe/src/bin/one_tx_worst.rs
step worst-build bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$S/release/one_tx_worst $B" || { echo WORST_BUILD_FAILED > $D; exit 1; }
SPECS=withdrawal:255:60:full,withdrawal:255:1:full,withdrawal:1023:1:full,withdrawal:254:1:full,withdrawal:0:1:genesis,transfer:255:1:full
step worst-run bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S taskset --cpu-list 0-3 $B $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/worst/gate-$N.json '$SPECS' $HEADELF $N=$E" || { echo WORST_RUN_FAILED > $D; exit 1; }
if [ $bad = 0 ]; then
  { echo OK; cat $M | head -16; cat $R7; sha256sum $E $W/worst/gate-$N.json $B; } > $D 2>&1
else
  [ -f $D ] || echo "FAILED (see tp1/gate1-$N.steps)" > $D
fi
echo "gate status: $(head -1 $D)" >> $ST
