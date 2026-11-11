#!/bin/bash
# Pool page zero check, v2 (helper as slice equality): build src-pool-final2 with the deployed recipe,
# run the Pool crate tests (deployed features, defaults), the old-against-new one_tx_worst runs (positive
# and negative scenario lists of pool-specs.sh) and the replays and redirect attempts. Old Pool and form A
# (v1) results are reused from pool-worst/{old,new}-{pos,neg}.json, not rerun.
# Time is expected in compilation (SBF build, native test build), then in proving (one fixture proof per
# scenario, seconds each). Attempt names PL2-*.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
S=src-pool-final2
P=$W/out/PL2-final2/artifacts/aspis_pool.so
TOOL=$W/pool-worst/one_tx_worst-pool
E=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so
FEATURES=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
. ./pool-specs.sh
diff -ruN src-xp1/programs/aspis-pool $S/programs/aspis-pool > pool-patches/final2.patch
bash fv_slot.sh PL2-build 3000 bash $W/fv_pool_build.sh PL2-final2 $S || { echo BUILD_FAILED; exit 1; }
echo "elf $(cat out/PL2-final2/so.sha256) $(awk '{print $5}' out/PL2-final2/so.size)"
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-test-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
bash fv_slot.sh PL2-test-deployed 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool --features $FEATURES" &
bash fv_slot.sh PL2-test-default 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool" &
wait
bash fv_slot.sh PL2-W-pos 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$P taskset --cpu-list 0-3 $TOOL $W/devnet/PIN2_TRANSACTIONS.json $P $W/pool-worst/new2-pos.json '$POS' X1=$E" &
bash fv_slot.sh PL2-W-neg 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$P taskset --cpu-list 0-3 $TOOL $W/devnet/PIN2_TRANSACTIONS.json $P $W/pool-worst/new2-neg.json '$NEG' X1=$E" &
for op in transfer withdrawal; do
  bash fv_slot.sh PL2-R-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$P $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $W/pool-replays/final2-$op.json"
done
bash fv_slot.sh PL2-RD 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$P $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $P $E $W/pool-replays/final2-redirect-withdrawal.json"
wait
sha256sum $P pool-patches/final2.patch pool-worst/new2-*.json pool-replays/final2-*.json
echo V2_DONE
