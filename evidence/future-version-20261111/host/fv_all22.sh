#!/bin/bash
# Branch-head build of the one-transaction adapter (transcript continuation, Merkle check last),
# rebuilt replay tools, replay of the recorded devnet settlements and the redirect attempts.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
E=$W/out/A6-onetx-head/artifacts/aspis_r1_cost_probe_program.so
bash fv_slot.sh B-A6-adapter 3000 bash $W/fv_build_adapter.sh A6-onetx-head $K || { echo ADAPTER_BUILD_FAILED > $W/ALL22_DONE; exit 1; }
bash fv_slot.sh B-D12-tools 3000 bash -c "cd $W/src/tools/r1-cost-probe && taskset --cpu-list 0-3 env -i HOME=/home/dombarker USER=dombarker PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin CARGO_HOME=/home/dombarker/.cargo CARGO_TARGET_DIR=$W/target/native CARGO_NET_OFFLINE=true CARGO_BUILD_JOBS=4 cargo +1.94.1 build --release --offline --locked --bin one_tx_replay --bin one_tx_redirect" || { echo TOOLS_BUILD_FAILED > $W/ALL22_DONE; exit 1; }
mkdir -p replays-v4
for op in transfer withdrawal; do
  bash fv_slot.sh R7-A6-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $E $op $W/replays-v4/A6-onetx-head-$op.json" || { echo REPLAY_FAILED_$op > $W/ALL22_DONE; exit 1; }
done
bash fv_slot.sh RD2-redirect 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $E $W/replays-redirect/A6-withdrawal.json"; echo "redirect exit $?" > $W/ALL22_DONE
