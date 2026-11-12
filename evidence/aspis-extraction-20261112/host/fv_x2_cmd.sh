#!/bin/bash
# X2 launcher for one auxiliary command (a scan, a census, cargo tree, one Lean file) in one fv_slot.sh scope.
# Usage: fv_x2_cmd.sh <attempt-suffix> <timeout-seconds> <status-dir> <cmd...>
#   attempt X2-<suffix>; receipt W/receipts/X2-<suffix> copied to <status-dir>/receipt-<suffix>; exit code in
#   <status-dir>/status-<suffix>; stdout/stderr of the command in the receipt.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
A=$1; TO=$2; SD=$3; shift 3
mkdir -p $SD
cd $W
bash $W/fv_slot.sh X2-$A $TO "$@" > $SD/launch-$A.log 2>&1
rc=$?
cp -r $W/receipts/X2-$A $SD/receipt-$A 2>/dev/null
echo $rc > $SD/status-$A
exit $rc
