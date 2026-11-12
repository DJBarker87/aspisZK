#!/bin/bash
# Host launcher: one capped user scope per job through tools/run_job.py (turn.sh, reservation check,
# MemoryHigh 6G, MemoryMax 8G, MemorySwapMax 0, TasksMax 256). Usage: job.sh NAME TIMEOUT "EXPECTED" CMD...
W=/home/dombarker/project-offloads/codex-pv-aspis-rewrite-20261111
N=$1; TO=$2; X=$3; shift 3
export PV_SRC_REV=$(cat $W/SOURCE_REVISION)
python3 $W/tools/run_job.py $N "$X" $TO $W -- "$@" > $W/runs/$N.driver.log 2>&1
rc=$?; tail -1 $W/runs/$N.driver.log; exit $rc
