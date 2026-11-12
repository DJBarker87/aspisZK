#!/bin/bash
# X2b: one emission and its native compile, INSIDE one fv_slot.sh scope (started by fv_x2b_job.sh).
#   1. fv_x2_run.py (X2's runner, unchanged) with the given stages (charon, aeneas or noabort, scan)
#   2. if the last argument is "native": fv_x2b_native.sh on the raw Aeneas output (release if present, else
#      noabort), zero edits, against X3's native Lean 4.36.0-rc2 library (read only, by reference)
# Usage: fv_x2b_emit.sh <config.json> <out dir> <stages> [native]
set -u
X=/home/dombarker/project-offloads/future-version-20261111/x2b
CFG=$1; OUT=$2; ST=$3; NAT=${4:-}
python3 -I $X/bin/fv_x2_run.py $CFG $OUT $ST
NS=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['ns'])" $CFG)
if [ "$NAT" = native ]; then
  R=$OUT/runs/A-release/raw/$NS; [ -f $R/Funs.lean ] || R=$OUT/runs/A-noabort/raw/$NS
  bash $X/bin/fv_x2b_native.sh $R $NS $OUT/native
  python3 -I $X/bin/fv_x2b_errs.py $OUT/native > $OUT/native/errors.txt
fi
