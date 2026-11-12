#!/bin/bash
# Runs INSIDE one fv_slot.sh scope. Aspis freeze: every check of the gates, on the FROZEN tree, with the tree's own
# tool sources (nothing is copied into the tree). Commands are those of fv_fz_gate_inner.sh; what differs:
#   - the program ELF is not built here: it is the freeze build given as an argument (fv_frz_build.sh);
#   - the mutant tool and the worst-case tool are built from the tree's own source files;
#   - the recorded payments and the redirect attempts are replayed twice: with the deployed Pool (as in every gate)
#     and with the frozen Pool;
#   - the worst-case run is the combined one (seven scenarios, frozen Pool), candidate ELF beside the frozen ELF.
# Comparison base: the candidate's gate `cand1` (tree src-cand1, commit 33e2d8475bc).
# Usage: fv_frz_checks.sh <name> <tree> <frozen verifier ELF (measurement ids)> <frozen pool ELF>
# Time is expected in compilation (four cold target directories), about 6 minutes of client-configuration tests,
# then about a minute of mutant runs and a minute of worst-case runs.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; S=$2; E=$3; POOL=$4
OUT=$W/frz/$N; test ! -e $OUT || { echo "exists: $OUT"; exit 2; }
mkdir -p $OUT/logs; ST=$OUT/steps.txt; : > $ST; LOGS=$OUT/logs
CAND_ELF=$W/out/cand1/artifacts/aspis_r1_cost_probe_program.so
BASE_OUT=$W/tp1/gate2-cand1; BASE_MUT=$W/mutants/g-cand1-src-cand1.txt
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
REV="$(cat $W/$S/FROZEN_COMMIT)"
bad=0
step() { local name=$1; shift; local t0=$(date +%s); "$@" > $LOGS/$name.log 2>&1; local rc=$?; echo "$name exit $rc; wall $(( $(date +%s) - t0 )) s" >> $ST; return $rc; }
note() { echo "$*" >> $ST; }
note "tree $S commit $REV files sha256 $(cat $W/$S/FROZEN_TREE_SHA256)"
note "verifier ELF $(sha256sum $E | cut -d' ' -f1); pool ELF $(sha256sum $POOL | cut -d' ' -f1)"
# 1 unit tests of the verifier crate, deployed settings with the prover
step unit-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --lib" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/unit-tests.log | head -5 >> $ST
# 2 client configuration
step client-config bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-client-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features r1p-check --lib -- prover sim" || bad=1
grep -E "test result|FAILED|panicked" $LOGS/client-config.log | head -5 >> $ST
# 3 program crate tests under the deployed settings and under the two-transaction settings; outcome lists against the candidate's
ptest() { # label, features, candidate-gate label
  step program-tests-$1 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-ptest-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe-program --features $2 --lib"
  grep -E "^test .* (ok|FAILED|ignored)$" $LOGS/program-tests-$1.log | sort > $OUT/program-tests-$1.outcomes
  local n=$(wc -l < $OUT/program-tests-$1.outcomes) f=$(grep -c 'FAILED$' $OUT/program-tests-$1.outcomes)
  if cmp -s $OUT/program-tests-$1.outcomes $BASE_OUT/program-tests-$3-src-cand1.outcomes; then note "program tests ($1): $n tests, $f failing; outcome list identical to the candidate's"; else note "program tests ($1): $n tests, $f failing; outcome list DIFFERS from the candidate's"; bad=1; fi
}
ptest deployed aspis deployed
ptest two-transaction pool-adapter,private-leaf-salts r1
# 4 integration tests
step integration-tests bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-test-$S cargo +1.94.1 test --release --offline --locked -p aspis-r1-cost-probe --features 'prover aspis' --test sampler_equivalence --test aspis_one_tx_statement_binding --test weights_equivalence --test pairing_equivalence --test dots_equivalence --test validated_prefix --test transport_equivalence --test domain_equivalence --test digest_schedule" || bad=1
note "integration tests: $(grep -c 'test result: ok' $LOGS/integration-tests.log) binaries ok, $(grep -c 'FAILED' $LOGS/integration-tests.log) FAILED lines"
# 5 recorded payments and redirect attempts, deployed Pool and frozen Pool
for pl in deployed frozen; do
  P=$W/devnet/pool.so; [ $pl = frozen ] && P=$POOL
  for op in transfer withdrawal; do
    step replay-$pl-$op bash -c "ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $OUT/replay-$pl-$op.json" || bad=1
  done
  step redirect-$pl bash -c "ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $P $E $OUT/redirect-$pl-withdrawal.json" || bad=1
done
# 6 mutant campaign with the tree's own tool: observed run and deployed run, against the candidate's files
mbuild() { step mutant-build$2 bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-mut-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_mutants --features '$1' && cp $W/target/native-mut-$S/release/one_tx_mutants $OUT/one_tx_mutants$2"; }
mrun() { step mutant-run$1 bash -c "taskset --cpu-list 0-3 $OUT/one_tx_mutants$1 $W/devnet/PIN2_TRANSACTIONS.json $OUT/mutants$1.txt 1 4"; }
strip() { awk '/^#/ {print; next} {NF=NF-1; print}' "$1"; }
if mbuild "aspis-r1-cost-probe/aspis aspis-r1-cost-probe/phase-observer" -observed && mrun -observed && mbuild "aspis-r1-cost-probe/aspis" -deployed && mrun -deployed; then
  sha256sum $OUT/mutants-observed.txt $BASE_MUT $OUT/mutants-deployed.txt $OUT/one_tx_mutants-observed $OUT/one_tx_mutants-deployed > $OUT/mutants.sha256
  strip $BASE_MUT > $OUT/mutants-candidate.verdicts.txt; strip $OUT/mutants-deployed.txt > $OUT/mutants-deployed.verdicts.txt
  sha256sum $OUT/mutants-candidate.verdicts.txt $OUT/mutants-deployed.verdicts.txt >> $OUT/mutants.sha256
  nz=$(awk '!/^#/ && $NF != 0' $OUT/mutants-deployed.txt | wc -l)
  if cmp -s $OUT/mutants-observed.txt $BASE_MUT && cmp -s $OUT/mutants-candidate.verdicts.txt $OUT/mutants-deployed.verdicts.txt && [ "$nz" = 0 ]; then note "mutants: observed run byte-identical to the candidate's ($(wc -l < $OUT/mutants-observed.txt) lines); deployed run verdicts identical, nonzero mark counts 0"; else note "mutants: DIFFERENT (nonzero marks $nz)"; bad=1; fi
else note "mutants: BUILD OR RUN FAILED"; bad=1; fi
# 7 combined worst-case run with the tree's own tool: seven scenarios, frozen Pool, candidate ELF beside the frozen ELF
step worst-build bash -c "cd $W/$S/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i $ENVV CARGO_TARGET_DIR=$W/target/native-wc-$S cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-$S/release/one_tx_worst $OUT/one_tx_worst" || bad=1
SPECS=withdrawal:255:60:full,withdrawal:255:1:full,withdrawal:254:1:full,withdrawal:3:1:full,withdrawal:0:1:genesis,transfer:255:1:full,transfer:3:1:full
step worst-run bash -c "ASPIS_SOURCE_REVISION=$REV taskset --cpu-list 0-3 $OUT/one_tx_worst $W/devnet/PIN2_TRANSACTIONS.json $POOL $OUT/cmb3.json '$SPECS' CAND1=$CAND_ELF FROZEN=$E" || bad=1
sha256sum $OUT/cmb3.json $OUT/one_tx_worst $OUT/replay-*.json $OUT/redirect-*.json >> $OUT/files.sha256 2>/dev/null
[ $bad = 0 ] && note "status: OK" || note "status: FAILED"
exit $bad
