#!/bin/bash
# X2d: one emission and its native compile, INSIDE one fv_slot.sh scope. fv_x2c_emit.sh with its helpers read from
# W/x2d/emitbin (a copy of W/x2c/bin, so that nothing is written under W/x2c):
#   1. fv_x2_run.py (X2's runner, unchanged) with the given stages
#   2. if the last argument is "native": fv_x2b_native.sh on the raw Aeneas output, zero edits, against X3's native
#      Lean 4.36.0-rc2 library (read only, by reference)
# Usage: fv_x2d_emit.sh <config.json> <out dir> <stages> [native]
set -u
X=/home/dombarker/project-offloads/future-version-20261111/x2d/emitbin
CFG=$1; OUT=$2; ST=$3; NAT=${4:-}
python3 -I $X/fv_x2_run.py $CFG $OUT $ST
NS=$(python3 -c "import json,sys;print(json.load(open(sys.argv[1]))['ns'])" $CFG)
if [ "$NAT" = native ]; then
  R=$OUT/runs/A-release/raw/$NS; [ -f $R/Funs.lean ] || R=$OUT/runs/A-noabort/raw/$NS
  bash $X/fv_x2b_native.sh $R $NS $OUT/native
  python3 -I $X/fv_x2b_errs.py $OUT/native > $OUT/native/errors.txt
fi
