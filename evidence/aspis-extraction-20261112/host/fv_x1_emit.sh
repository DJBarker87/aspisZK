#!/bin/bash
# X1: one emission run of the deployed verifier program in ONE fv_slot.sh scope (MemoryHigh 6G, MemoryMax 8G, no
# swap; never raised). Usage: fv_x1_emit.sh <run-config.json> <label> <timeout-seconds>
# Output: W/x1/runs/<label>; receipt W/receipts/X1-<label>; exit code also in W/x1/runs/<label>.exit.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x1
[ $# -eq 3 ] || { echo "usage: fv_x1_emit.sh <config> <label> <timeout>"; exit 2; }
CFG=$1; LABEL=$2; TO=$3
test ! -e $X/runs/$LABEL || { echo "output exists: $X/runs/$LABEL"; exit 2; }
mkdir -p $X/runs/$LABEL
cd $W
bash fv_slot.sh X1-$LABEL $TO python3 -I $X/bin/fv_x1_run.py $CFG $X/runs/$LABEL > $X/runs/$LABEL.slot.log 2>&1
rc=$?
echo $rc > $X/runs/$LABEL.exit
exit $rc
