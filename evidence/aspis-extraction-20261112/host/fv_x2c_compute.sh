#!/bin/bash
# X2c step 7(d): compute of the two recorded payments with the frozen verifier and (1) the frozen Pool, (2) the Pool
# built from the rewrite tree. Runs INSIDE one fv_slot.sh scope. Time is expected in compilation (one SBF build of
# the Pool and its two Aspis crates, cold target directory), then four replays of about a second each.
# The replay tool exits non-zero with a Pool that is not the recorded one (its two-transaction control differs);
# the compute figures are read from its output file in both cases.
# Usage: fv_x2c_compute.sh <attempt> <tree name directly under W (src-x2c-<n>)> <out dir>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; S=$2; O=$3; mkdir -p $O
E=$W/out/frz-a-meas/artifacts/aspis_r1_cost_probe_program.so
FRZ=$W/out/PL-frz-a/artifacts/aspis_pool.so
REV="$(cat $W/src-frz-a/FROZEN_COMMIT)"
echo "== build"; bash $W/fv_pool_build.sh $A $S > $O/build.log 2>&1; echo "build exit $?"
NEW=$W/out/$A/artifacts/aspis_pool.so
sha256sum $E $FRZ $NEW $W/devnet/verifier-pin2.so $W/devnet/PIN2_TRANSACTIONS.json $W/target/native/release/one_tx_replay > $O/inputs.sha256
grep -iE "stack offset|exceeded|warning: .*stack" $O/build.log | head -20 > $O/stack-warnings.txt
for pl in frozen x2c; do
  P=$FRZ; [ $pl = x2c ] && P=$NEW
  for op in transfer withdrawal; do
    ASPIS_SOURCE_REVISION=$REV $W/target/native/release/one_tx_replay $W/devnet/PIN2_TRANSACTIONS.json $P $W/devnet/verifier-pin2.so $E $op $O/replay-$pl-$op.json > $O/replay-$pl-$op.log 2>&1
    echo "replay $pl $op exit $?"
  done
done
