#!/bin/bash
# X1b: compile the RAW Aeneas output of one X1b run against the native Aeneas library (X3's build under W/x3, objects
# by reference, never written), ZERO edits: Types.lean and Funs.lean byte-copied, the two generated templates copied to
# the module names their siblings import. X1's fv_x1_probe.sh with the X1b paths. Runs INSIDE one fv_slot.sh scope.
# Usage: fv_x1b_probe.sh <run-label> [release|noabort]
set -u
W=/home/dombarker/project-offloads/future-version-20261111
L=$1; MODE=${2:-release}; NS=AspisX1
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
RAW=$W/x1b/runs/$L/runs/A-$MODE/raw/$NS
D=$W/x1b/probe/$L
test ! -e $D || { echo "exists: $D"; exit 2; }
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
  /usr/bin/time -v -o $D/$M.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 2400 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -DmaxErrors=100000 -R $D/src -o $D/out/$NS/$M.olean $D/src/$NS/$M.lean > $D/$M.log 2>&1
  echo "$M $? errors $(grep -c ': error' $D/$M.log) peak_kb $(grep 'Maximum resident' $D/$M.time | awk '{print $NF}') wall $(grep 'Elapsed' $D/$M.time | awk '{print $NF}')" >> $D/exit.txt
done
