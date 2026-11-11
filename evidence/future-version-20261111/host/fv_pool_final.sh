#!/bin/bash
# Pool final ELF for the freeze: build the Pool from src-head3 (the current head, never modified here)
# with the deployed recipe; rebuild the one_tx_worst tool with the account-corruption modes; run the
# Pool crate tests in src-head3 (deployed features, defaults); run old (deployed) and new Pool against
# the head's verifier ELF (out/BASE2) over the positive list, the page-negative list and the
# account-negative list; replay the recorded payments and the redirect attempts with both Pools.
# Time is expected in compilation first (SBF build, incremental tool build, native test build), then in
# proving (one fixture proof per scenario, seconds to tens of seconds each). Attempt names PL3-*.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
S=src-head3
NEW=$W/out/PL3-head3/artifacts/aspis_pool.so
OLD=$W/devnet/pool.so
E=$W/out/BASE2/artifacts/aspis_r1_cost_probe_program.so
TOOL=$W/pool-worst/one_tx_worst-pool3
FEATURES=r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit
. ./pool-specs.sh
ACC="withdrawal:3:1:neg-master-0,withdrawal:3:1:neg-master-40,withdrawal:3:1:neg-master-49,withdrawal:3:1:neg-master-64,withdrawal:3:1:neg-master-320,withdrawal:3:1:neg-master-383,withdrawal:3:1:neg-checkpoint-0,withdrawal:3:1:neg-checkpoint-8,withdrawal:3:1:neg-checkpoint-72,withdrawal:3:1:neg-checkpoint-80,withdrawal:3:1:neg-checkpoint-112,withdrawal:3:1:neg-checkpoint-191,withdrawal:3:1:neg-lane-0,withdrawal:3:1:neg-lane-40,withdrawal:3:1:neg-lane-80"
mkdir -p pool-final
bash fv_slot.sh PL3-build 3000 bash $W/fv_pool_build.sh PL3-head3 $S &
cp pool-stage/one_tx_worst.rs src-pool-tool/tools/r1-cost-probe/src/bin/one_tx_worst.rs
bash fv_slot.sh PL3-tool-build 3000 bash -c "cd $W/src-pool-tool/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-wc-src-pool-tool CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin one_tx_worst && cp $W/target/native-wc-src-pool-tool/release/one_tx_worst $TOOL" &
wait
test -s $NEW || { echo BUILD_FAILED; exit 1; }
test -x $TOOL || { echo TOOL_BUILD_FAILED; exit 1; }
echo "elf $(cat out/PL3-head3/so.sha256) $(awk '{print $5}' out/PL3-head3/so.size)"
ENVV="HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native-test-$S CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4"
bash fv_slot.sh PL3-test-deployed 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool --features $FEATURES" &
for side in old new; do
  if [ $side = old ]; then P=$OLD; else P=$NEW; fi
  for kind in pos neg acc; do
    case $kind in pos) SP="$POS";; neg) SP="$NEG";; acc) SP="$ACC";; esac
    bash fv_slot.sh PL3-W-$side-$kind 5400 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SRC_HEAD3_COMMIT)+pool:$P taskset --cpu-list 0-3 $TOOL $W/devnet/PIN2_TRANSACTIONS.json $P $W/pool-final/$side-$kind.json '$SP' BASE2=$E" &
  done
done
wait
bash fv_slot.sh PL3-test-default 3000 bash -c "cd $W/$S && taskset --cpu-list 0-3 env -i $ENVV cargo +1.94.1 test --release --offline --locked -p aspis-pool"
for side in old new; do
  if [ $side = old ]; then P=$OLD; else P=$NEW; fi
  for op in transfer withdrawal; do
    bash fv_slot.sh PL3-R-$side-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SRC_HEAD3_COMMIT)+pool:$P $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $W/pool-final/replay-$side-$op.json"
  done
  bash fv_slot.sh PL3-RD-$side 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SRC_HEAD3_COMMIT)+pool:$P $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $P $E $W/pool-final/redirect-$side-withdrawal.json"
done
sha256sum $NEW $OLD $E $TOOL pool-stage/one_tx_worst.rs pool-final/*.json
echo FINAL_DONE
