#!/bin/bash
# X1b: the two recorded-payment replay steps of the lead's fv_frz_checks.sh (step 5, frozen Pool only), unchanged
# command lines, for one verifier ELF. Runs INSIDE one fv_slot.sh scope. Usage: fv_x1b_replay.sh <label> <verifier ELF>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
L=$1; E=$2; POOL=$W/out/PL-frz-a/artifacts/aspis_pool.so; OUT=$W/x1b/replay/$L
test ! -e $OUT || { echo "exists: $OUT"; exit 2; }
mkdir -p $OUT; REV="$(cat $W/src-frz-a/FROZEN_COMMIT)"
sha256sum $E $POOL > $OUT/inputs.sha256
for op in transfer withdrawal; do
  ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $POOL $W/devnet/verifier-pin2.so $E $op $OUT/replay-$op.json > $OUT/replay-$op.log 2>&1
  echo "$op exit $?"
done
