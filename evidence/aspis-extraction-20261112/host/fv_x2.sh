#!/bin/bash
# X2 launcher: one fv_slot.sh scope (MemoryHigh 6G, MemoryMax 8G, no swap; never raised) running fv_x2_run.py.
# Usage: fv_x2.sh <attempt-suffix> <timeout-seconds> <config.json> <out-dir> <stages>
#   attempt name X2-<attempt-suffix>; receipt W/receipts/X2-<suffix>; exit code written to <out-dir>/status-<suffix>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x2
A=$1; TO=$2; CFG=$3; OUT=$4; ST=$5
mkdir -p $OUT
cd $W
bash $W/fv_slot.sh X2-$A $TO python3 -I $X/bin/fv_x2_run.py $CFG $OUT $ST > $OUT/launch-$A.log 2>&1
rc=$?
cp -r $W/receipts/X2-$A $OUT/receipt-$A 2>/dev/null
echo $rc > $OUT/status-$A
exit $rc
