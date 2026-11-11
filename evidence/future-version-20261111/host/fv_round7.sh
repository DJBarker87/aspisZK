#!/bin/bash
# Round 7: build a patched copy of the branch head and replay the recorded devnet settlements and
# the redirect attempts against it. Usage: fv_round7.sh <attempt> <source-dir-name>
# Time is expected in compilation (the SBF build); each replay is seconds.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
A=$1; S=$2
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
E=$W/out/$A/artifacts/aspis_r1_cost_probe_program.so
D=$W/ROUND7_$A.done; rm -f $D
bash fv_slot.sh B-$A 3000 bash $W/fv_build_adapter_src.sh $A $K $S || { echo BUILD_FAILED > $D; exit 1; }
mkdir -p replays-v5 replays-redirect
for op in transfer withdrawal; do
  bash fv_slot.sh R8-$A-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $E $op $W/replays-v5/$A-$op.json" || { echo REPLAY_FAILED_$op > $D; exit 1; }
done
bash fv_slot.sh RD3-$A 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+$S $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $E $W/replays-redirect/$A-withdrawal.json"; echo "redirect exit $?" > $D
