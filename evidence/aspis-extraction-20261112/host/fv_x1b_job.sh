#!/bin/bash
# X1b: one emission of a rewrite tree, then the zero-edit native compile of the RAW output, then the gates. Runs INSIDE
# one fv_slot.sh scope (MemoryHigh 6G, MemoryMax 8G, no swap). Usage (from W):
#   bash fv_slot.sh X1b-<label> 5400 bash x1b/bin/fv_x1b_job.sh <label> <config.json> [release|noabort]
set -u
W=/home/dombarker/project-offloads/future-version-20261111; X=$W/x1b
L=$1; CFG=$2; MODE=${3:-release}
test ! -e $X/runs/$L || { echo "exists: $X/runs/$L"; exit 2; }
mkdir -p $X/runs/$L
python3 -I $X/bin/fv_x1b_run.py $CFG $X/runs/$L > $X/runs/$L.run.log 2>&1; echo "run exit $?"
R=$X/runs/$L/runs/A-$MODE/raw/AspisX1
[ -f $R/Funs.lean ] || { echo "no Funs.lean for $MODE"; exit 3; }
bash $X/bin/fv_x1b_probe.sh $L $MODE; echo "probe exit $?"
python3 -I $X/bin/fv_x1b_aspis_axioms.py $R > $X/runs/$L/aspis-axioms.tsv; echo "axioms exit $?"
python3 -I $X/bin/fv_x1b_writecalls.py $X/runs/$L/runs/C/out.llbc > $X/runs/$L/write-calls.tsv; echo "writecalls exit $?"
python3 -I $X/bin/fv_x1b_errs.py $X/probe/$L > $X/probe/$L/errors.tsv; echo "errs exit $?"
cat $X/probe/$L/exit.txt
