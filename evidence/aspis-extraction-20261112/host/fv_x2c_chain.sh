#!/bin/bash
# X2c: the step 5 to 7 runs in sequence, ONE fv_slot.sh scope at a time (each its own attempt):
#   tests of the frozen copy (baseline counts, recorder dumps), tests of the rewrite tree, the single-root emission
#   and native compile, then the compute build and replays from a copy of the rewrite tree at W/<tree>.
# Usage: fv_x2c_chain.sh <suffix> <tree name src-x2c-<n>>   (run with nohup; writes W/x2c/chain-<suffix>.status)
set -u
W=/home/dombarker/project-offloads/future-version-20261111
X=$W/x2c; N=$1; T=$2
cd $W
bash fv_slot.sh X2c-test-frz-$N 3000 bash $X/bin/fv_x2c_test.sh $X/frz-test-tree frz $X/dump-frz-$N "" > $X/chain-$N.log 2>&1
bash fv_slot.sh X2c-test-$N 3000 bash $X/bin/fv_x2c_test.sh $X/rw-tree rw $X/dump-rw-$N "" >> $X/chain-$N.log 2>&1
python3 -I $X/bin/fv_x2c_compare_dumps.py $X/dump-frz-$N $X/dump-rw-$N > $X/compare-$N.txt 2>&1
bash $X/bin/fv_x2c_job.sh pool-$N 3000 $X/pool-$N bash $X/bin/fv_x2c_emit.sh $X/config/fv_x2c_cfg_$N.json $X/pool-$N charon,aeneas,scan native >> $X/chain-$N.log 2>&1
test -e $W/$T || cp -a $X/rw-tree $W/$T
bash fv_slot.sh X2c-compute-$N 3000 bash $X/bin/fv_x2c_compute.sh X2c-build-$N $T $X/compute-$N >> $X/chain-$N.log 2>&1
echo done > $X/chain-$N.status
