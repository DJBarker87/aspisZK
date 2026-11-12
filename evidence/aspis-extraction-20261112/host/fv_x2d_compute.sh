#!/bin/bash
# X2d item 4: compute of all four Pool handlers, recorded devnet transactions (W/devnet/PIN2_TRANSACTIONS.json),
# LiteSVM. Runs INSIDE one fv_slot.sh scope; time is in about twenty replays of a second or two each.
#   initialize, deposit-0, deposit-1, checkpoint: x2d_pool_replay (this task's tool; first ELF = the deployed devnet
#     Pool as control, which must reproduce the recorded Pool compute and post-state); then one ELF per label.
#   transfer, withdrawal (settlement): the lead's one_tx_replay, unchanged (frozen one-transaction verifier ELF
#     out/frz-a-meas, deployed verifier pin2 for its control), once per labelled Pool ELF, as X2c's fv_x2c_compute.sh.
# Usage: fv_x2d_compute.sh <out dir> <label=pool.so>[,<label=pool.so>...]
set -u
W=/home/dombarker/project-offloads/future-version-20261111
O=$1; ELFS=$2; mkdir -p $O
E=$W/out/frz-a-meas/artifacts/aspis_r1_cost_probe_program.so
REV="$(cat $W/src-x2d-1/FROZEN_COMMIT)+x2d"
sha256sum $W/devnet/pool.so $E $W/devnet/verifier-pin2.so $W/devnet/PIN2_TRANSACTIONS.json $W/target/native/release/one_tx_replay $W/x2d/bin/x2d_pool_replay $(echo $ELFS | tr ',' '\n' | cut -d= -f2) > $O/inputs.sha256
ASPIS_SOURCE_REVISION=$REV $W/x2d/bin/x2d_pool_replay $W/devnet/PIN2_TRANSACTIONS.json control=$W/devnet/pool.so,$ELFS pool-initialize,deposit-0,deposit-1,forest-checkpoint $O/handlers.json > $O/handlers.log 2>&1
echo "handlers exit $?"
for pair in $(echo $ELFS | tr ',' ' '); do
  label=${pair%%=*}; P=${pair#*=}
  for op in transfer withdrawal; do
    ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $O/replay-$label-$op.json > $O/replay-$label-$op.log 2>&1
    echo "replay $label $op exit $?"
  done
done
