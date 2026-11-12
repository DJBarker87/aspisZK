#!/bin/bash
# X3 stage B: compile the RAW Aeneas emission of one scope against the native library, zero edits, zero shims.
# NOT RUN on 2026-11-12 (stage A not built). Runs INSIDE one fv_slot.sh scope:
#   bash W/fv_slot.sh X3-B-<scope> 1800 bash W/x3/bin/fv_x3_probe.sh <scope-letter> <namespace>
#   scopes: v AspisTPv, p AspisTPp, s AspisTP2g, d AspisTP3stmt, c AspisTP3core
# The files are byte copies of frz-emit/frza/runs/A-<s>-release/raw/<ns>/. The two templates are copied to the
# file names that Types/Funs import (<ns>/TypesExternal.lean, <ns>/FunsExternal.lean): a rename, no content edit.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
S=$1; NS=$2
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
RAW=$W/frz-emit/frza/runs/A-$S-release/raw/$NS
D=$W/x3/probe/$S
mkdir -p $D/src/$NS $D/out
cp $RAW/Types.lean $RAW/Funs.lean $D/src/$NS/
[ -f $RAW/TypesExternal_Template.lean ] && cp $RAW/TypesExternal_Template.lean $D/src/$NS/TypesExternal.lean
cp $RAW/FunsExternal_Template.lean $D/src/$NS/FunsExternal.lean
sha256sum $RAW/*.lean $D/src/$NS/*.lean > $D/inputs.sha256
LP=$D/out:$B/.lake/build/lib/lean
for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
for M in TypesExternal Types FunsExternal Funs; do
  [ -f $D/src/$NS/$M.lean ] || continue
  mkdir -p $D/out/$NS
  /usr/bin/time -v -o $D/$M.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 900 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -R $D/src -o $D/out/$NS/$M.olean $D/src/$NS/$M.lean > $D/$M.log 2>&1
  echo "$M $?" >> $D/exit.txt
done
