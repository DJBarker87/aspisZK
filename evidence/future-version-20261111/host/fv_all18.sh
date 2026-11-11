#!/bin/bash
# Devnet preparation: lean one-transaction adapter (no stage 1 entry), the client, and the
# replay of the recorded devnet settlements against the lean adapter.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
K=pool-adapter,future-one-tx-lean,private-leaf-salts,future-fast-kmul,future-fast-prepared,future-fast-square,future-validated-decode,future-merkle-single-pass,future-tight-base,future-tight-weights,future-lazy-boundary,future-d-inactive-tensor,future-d-pair-expansion,future-merkle-in-place,future-lazy-horner,future-fold-shared
bash fv_scope.sh A5-onetx-lean 3000 bash $W/fv_build_adapter.sh A5-onetx-lean $K || { echo ADAPTER_BUILD_FAILED > $W/ALL18_DONE; exit 1; }
bash fv_scope.sh C1-client 3000 bash $W/fv_client_build.sh || { echo CLIENT_BUILD_FAILED > $W/ALL18_DONE; exit 1; }
mkdir -p replays-v3
for op in transfer withdrawal; do
  bash fv_scope.sh R6-A5-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $W/out/A5-onetx-lean/artifacts/aspis_r1_cost_probe_program.so $op $W/replays-v3/A5-onetx-lean-$op.json"
done
echo done > $W/ALL18_DONE
