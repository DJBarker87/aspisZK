#!/bin/bash
# X2c launcher (copy of fv_x2b_job.sh): one command in one fv_slot.sh scope (MemoryHigh 6G, MemoryMax 8G, no swap; never raised).
# Usage: fv_x2c_job.sh <attempt-suffix> <timeout-seconds> <status-dir> <cmd...>
#   attempt X2c-<suffix>; receipt W/receipts/X2c-<suffix> copied to <status-dir>/receipt-<suffix>;
#   exit code in <status-dir>/status-<suffix> (written last: the waiter polls for it).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; TO=$2; SD=$3; shift 3
mkdir -p $SD
cd $W
bash $W/fv_slot.sh X2c-$A $TO "$@" > $SD/launch-$A.log 2>&1
rc=$?
cp -r $W/receipts/X2c-$A $SD/receipt-$A 2>/dev/null
echo $rc > $SD/status-$A
exit $rc
