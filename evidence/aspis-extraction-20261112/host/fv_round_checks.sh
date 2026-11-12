#!/bin/bash
# Runs INSIDE one fv_slot.sh scope. Aspis rewrite rounds: every check of the freeze gate (fv_frz_checks.sh), on a
# round's tree, against the FROZEN tree's results (host directory frz/c1, tree src-frz-a, commit 3d700effcab).
# What differs from fv_frz_checks.sh:
#   - the comparison base is the frozen gate frz/c1 and the frozen ELFs, not the earlier candidate;
#   - a round adds tests, so test outcome lists are compared as "every test of the base has the same outcome";
#     tests that exist only in the round are listed, and all of them must pass;
#   - the recorded payments are replayed with the deployed Pool, the frozen Pool and the round's Pool, and the
#     compute of each is written beside the frozen figure;
#   - the worst-case run is made twice: frozen Pool with the frozen and the round verifier side by side, and the
#     round's Pool with the round verifier.
# Usage: fv_round_checks.sh <name> <tree> <round verifier ELF (measurement ids)> <round pool ELF> [intended-removals.tsv]
# intended-removals.tsv (tab-separated, '#' comments): test name as cargo prints it, the configuration it is absent
# from (deployed | two-transaction), the reason, the configuration in which it still runs and must pass.
# A program-test configuration passes only if: no test of the base changes its outcome; the tests of the base that
# are absent are exactly the listed ones for that configuration; no listed test is present there; every listed test
# passes in the configuration where it still runs; every test only in the round passes.
# Time is expected in compilation (four cold target directories), about 6 minutes of client-configuration tests,
# then about a minute of mutant runs and two minutes of worst-case runs.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; E=$3; POOL=$4; REMOVALS=${5:-}
OUT=$W/rounds/$N; test ! -e $OUT || { echo "exists: $OUT"; exit 2; }
mkdir -p $OUT/logs; ST=$OUT/steps.txt; : > $ST; LOGS=$OUT/logs
BASE=$W/frz/c1
FRZ_ELF=$W/out/frz-a-meas/artifacts/aspis_r1_cost_probe_program.so
FRZ_POOL=$W/out/PL-frz-a/artifacts/aspis_pool.so
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
REV="$(cat $W/$S/FROZEN_COMMIT)"
bad=0
step() { local name=$1; shift; local t0=$(date +%s); "$@" > $LOGS/$name.log 2>&1; local rc=$?; echo "$name exit $rc; wall $(( $(date +%s) - t0 )) s" >> $ST; return $rc; }
note() { echo "$*" >> $ST; }
note "tree $S commit $REV files sha256 $(cat $W/$S/FROZEN_TREE_SHA256)"
note "round verifier ELF $(sha256sum $E | cut -d' ' -f1); round pool ELF $(sha256sum $POOL | cut -d' ' -f1)"
note "frozen verifier ELF $(sha256sum $FRZ_ELF | cut -d' ' -f1); frozen pool ELF $(sha256sum $FRZ_POOL | cut -d' ' -f1)"
[ "$(sha256sum $E | cut -d' ' -f1)" = "$(sha256sum $FRZ_ELF | cut -d' ' -f1)" ] && note "verifier ELF: byte-identical to the frozen one" || note "verifier ELF: DIFFERS from the frozen one"
[ "$(sha256sum $POOL | cut -d' ' -f1)" = "$(sha256sum $FRZ_POOL | cut -d' ' -f1)" ] && note "pool ELF: byte-identical to the frozen one" || note "pool ELF: DIFFERS from the frozen one"
# outcome comparison with intended removals (the same file is used by the harness test)
source $W/fv_round_outcomes.sh
# 1 unit tests of the verifier crate, deployed settings with the prover
step unit-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --lib" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/unit-tests.log | head -5 >> $ST
# 1b unit tests of the core and statement crates (the rewrites add differential tests there)
step core-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-core --lib" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/core-tests.log | head -5 >> $ST
step statement-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-statement --features r0,pool-v1-kernel --lib" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/statement-tests.log | head -5 >> $ST
# 2 client configuration
step client-config bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-client-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features r1p-check --lib -- prover sim" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/client-config.log | head -5 >> $ST
# 3 program crate tests under the deployed settings and under the two-transaction settings
ptest() { # label, features
  step program-tests-$1 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features $2 --lib"
  outcomes $LOGS/program-tests-$1.log > $OUT/program-tests-$1.outcomes
  cmp_outcomes "program tests ($1)" $1 $OUT/program-tests-$1.outcomes $BASE/program-tests-$1.outcomes
}
ptest deployed aspis
ptest two-transaction pool-adapter,private-leaf-salts
lp=$(check_listed_pass); [ -n "$lp" ] && echo "$lp" >> $ST; echo "$lp" | grep -q "DOES NOT PASS" && bad=1
# 3b Pool crate tests, deployed feature list
step pool-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-pooltest-$S cargo +1.94.1 test --release --offline --locked -p aspis-pool --features r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/pool-tests.log | head -8 >> $ST
# 4 integration tests
step integration-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule" || bad=1
note "integration tests: $(grep -c 'test result: ok' $LOGS/integration-tests.log) binaries ok, $(grep -c 'FAILED' $LOGS/integration-tests.log) FAILED lines"
# 5 recorded payments and redirect attempts: deployed Pool, frozen Pool, round Pool
# (one_tx_replay exits non-zero by design when the Pool is not the recorded one; its conditions are in the JSON)
for pl in deployed frozen round; do
  P=$W/devnet/pool.so; [ $pl = frozen ] && P=$FRZ_POOL; [ $pl = round ] && P=$POOL
  for op in transfer withdrawal; do
    step replay-$pl-$op bash -c "ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $OUT/replay-$pl-$op.json"
    rc=$?; [ $pl = deployed ] && [ $rc != 0 ] && bad=1
  done
  step redirect-$pl bash -c "ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $P $E $OUT/redirect-$pl-withdrawal.json" || bad=1
done
note "replay files: compare the compute fields of $OUT/replay-*.json with $BASE/replay-*.json (frozen: deployed Pool 1,281,351 and 1,287,871; frozen Pool 1,232,920 and 1,239,440)"
# 6 mutant campaign with the tree's own tool: observed run and deployed run, against the frozen gate's files
mbuild() { step mutant-build$2 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-mut-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$1' && cp $W/target/native-mut-$S/release/one_tx_mutants $OUT/one_tx_mutants$2"; }
mrun() { step mutant-run$1 bash -c "taskset --cpu-list 0-3 $OUT/one_tx_mutants$1 $W/devnet/PIN2_TRANSACTIONS.json $OUT/mutants$1.txt 1 4"; }
strip() { awk '/^#/ {print; next} {NF=NF-1; print}' "$1"; }
if mbuild "aspis-r1-cost-probe/aspis aspis-r1-cost-probe/phase-observer" -observed && mrun -observed && mbuild "aspis-r1-cost-probe/aspis" -deployed && mrun -deployed; then
  strip $OUT/mutants-deployed.txt > $OUT/mutants-deployed.verdicts.txt
  sha256sum $OUT/mutants-observed.txt $BASE/mutants-observed.txt $OUT/mutants-deployed.verdicts.txt $BASE/mutants-deployed.verdicts.txt > $OUT/mutants.sha256
  nz=$(awk '!/^#/ && $NF != 0' $OUT/mutants-deployed.txt | wc -l)
  if cmp -s $OUT/mutants-observed.txt $BASE/mutants-observed.txt && cmp -s $OUT/mutants-deployed.verdicts.txt $BASE/mutants-deployed.verdicts.txt && [ "$nz" = 0 ]; then note "mutants: observed run byte-identical to the frozen gate's ($(wc -l < $OUT/mutants-observed.txt) lines); deployed run verdicts identical, nonzero mark counts 0"; else note "mutants: DIFFERENT (nonzero marks $nz)"; bad=1; fi
else note "mutants: BUILD OR RUN FAILED"; bad=1; fi
# 7 worst-case runs with the tree's own tool: seven scenarios
step worst-build bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$S/release/one_tx_worst $OUT/one_tx_worst" || bad=1
SPECS=withdrawal:255:60:full,withdrawal:255:1:full,withdrawal:254:1:full,withdrawal:3:1:full,withdrawal:0:1:genesis,transfer:255:1:full,transfer:3:1:full
step worst-run-frozen-pool bash -c "ASPIS_SOURCE_REVISION=$REV taskset --cpu-list 0-3 $OUT/one_tx_worst $W/devnet/PIN2_TRANSACTIONS.json $FRZ_POOL $OUT/worst-frozen-pool.json '$SPECS' FROZEN=$FRZ_ELF ROUND=$E" || bad=1
step worst-run-round-pool bash -c "ASPIS_SOURCE_REVISION=$REV taskset --cpu-list 0-3 $OUT/one_tx_worst $W/devnet/PIN2_TRANSACTIONS.json $POOL $OUT/worst-round-pool.json '$SPECS' ROUND=$E" || bad=1
note "worst case: compare $OUT/worst-frozen-pool.json (FROZEN against ROUND verifier, frozen Pool) and $OUT/worst-round-pool.json with $BASE/cmb3.json (frozen heaviest 1,262,410); the proof hashes in both must equal the frozen gate's"
sha256sum $OUT/worst-*.json $OUT/one_tx_worst $OUT/replay-*.json $OUT/redirect-*.json >> $OUT/files.sha256 2>/dev/null
[ $bad = 0 ] && note "status: PASSED" || note "status: FAILED"
exit $bad
