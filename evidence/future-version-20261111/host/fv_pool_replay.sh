#!/bin/bash
# Pool page zero check: replay the two recorded devnet settlements and the redirect attempts with a
# CHANGED Pool ELF (the verifier ELFs as in fv_round7.sh: deployed verifier for the control, X1 for the
# one-transaction runs). The deployed-Pool baseline is replays-v5/X1-rewrites-*.json and
# replays-redirect/X1-rewrites-withdrawal.json (not rerun).
# Note: one_tx_replay exits non-zero when the control's Pool CU differs from the recorded devnet
# figure, which a cheaper Pool does by design; it writes its JSON before that check.
# Usage: fv_pool_replay.sh <name> <pool.so>. Time: seconds per replay.
W=/home/dombarker/project-offloads/future-version-20261111
cd $W
N=$1; POOL=$2
E=$W/out/X1-rewrites/artifacts/aspis_r1_cost_probe_program.so
mkdir -p pool-replays
for op in transfer withdrawal; do
  bash fv_slot.sh PL-R-$N-$op 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$POOL $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $POOL $W/devnet/verifier-pin2.so $E $op $W/pool-replays/$N-$op.json"
  echo "replay $N $op exit $?"
done
bash fv_slot.sh PL-RD-$N 600 bash -c "ASPIS_SOURCE_REVISION=\$(cat $W/SOURCE_REVISION)+pool:$POOL $W/target/native/release/one_tx_redirect $W/devnet/PIN2_TRANSACTIONS.json $POOL $E $W/pool-replays/$N-redirect-withdrawal.json"
echo "redirect $N exit $?"
sha256sum $POOL pool-replays/$N-*.json
