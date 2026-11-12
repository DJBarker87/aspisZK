#!/bin/bash
# X1b: one item's evidence in ONE fv_slot.sh scope: emission + native probe + gates (fv_x1b_job.sh), cargo tests
# (fv_x1b_test.sh), SBF build (fv_x1b_build.sh). Usage (from W, long jobs with nohup):
#   bash fv_slot.sh X1b-item-<label> 7200 bash x1b/bin/fv_x1b_item.sh <label> <config> <build n> <aspis|both|none> <test steps...>
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1b
L=$1; CFG=$2; N=$3; B=$4; shift 4
echo "== job $(date -u +%T)"; bash $X/bin/fv_x1b_job.sh $L $CFG
if [ $# -gt 0 ]; then echo "== tests $(date -u +%T)"; bash $X/bin/fv_x1b_test.sh rw-tree "$@" > $X/logs/test-$L.log 2>&1; grep -E "^STEP|test result" $X/logs/test-$L.log; fi
if [ $B != none ]; then echo "== build $(date -u +%T)"; bash $X/bin/fv_x1b_build.sh rw-tree $N $B; fi
echo "== done $(date -u +%T)"
