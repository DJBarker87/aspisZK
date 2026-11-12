#!/bin/bash
# X2b (copy of fv_x2_native.sh, outputs under W/x2b): compile the RAW Aeneas output of one Pool emission against the native Aeneas Lean library of the pinned commit
# (X3's build under W/x3, read only, by reference), zero edits, zero shims: fv_x3_probe.sh with the input and output
# directories as arguments and everything written under the given directory. The two templates are copied to the names Types/Funs
# import (a rename, no content edit). Runs INSIDE one fv_slot.sh scope.
# Usage: fv_x2_native.sh <raw dir (…/raw/AspisX2)> <namespace> <out dir under W/x2b>
set -u
W=/home/dombarker/project-offloads/future-version-20261111
RAW=$1; NS=$2; D=$3
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
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
