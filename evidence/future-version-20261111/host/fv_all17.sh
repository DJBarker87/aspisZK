#!/bin/bash
# Round 5, third pass: rebuilt replay tool (devnet rent, state checks), same adapter ELF A4.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
bash fv_scope.sh D10-driver 3000 bash $W/fv_driver_build.sh || { echo DRIVER_BUILD_FAILED > $W/ALL17_DONE; exit 1; }
mkdir -p replays-v2
for op in transfer withdrawal; do
  bash fv_scope.sh R5-A4-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION) $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $W/devnet/pool.so $W/devnet/verifier-pin2.so $W/out/A4-onetx-summed/artifacts/aspis_r1_cost_probe_program.so $op $W/replays-v2/A4-onetx-summed-$op.json"
done
echo done > $W/ALL17_DONE
