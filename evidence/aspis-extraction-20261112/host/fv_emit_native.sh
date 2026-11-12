#!/bin/bash
# X7: compile the RAW Aeneas output of one program against the translator's own Lean library (X3's build of the
# pinned Aeneas commit 0d21a9ec under W/x3, Lean 4.36.0-rc2, objects by reference, never written), ZERO edits:
# Types.lean and Funs.lean byte-copied; the two generated templates byte-copied to the module names their siblings
# import (<ns>/TypesExternal.lean, <ns>/FunsExternal.lean): a rename, no content edit. No shim, no rule.
# The method of X1b's fv_x1b_probe.sh and X2b's fv_x2b_native.sh (timeout 2400 s per module, -DmaxErrors=100000 so
# that every error is listed). Runs INSIDE the fv_slot.sh scope of fv_emit_job.sh.
# Usage: fv_emit_native.sh <raw dir (.../raw/<ns>)> <ns> <out dir>
# Output: <out>/exit.txt, one line per module: "<module> <exit> errors <n> peak_kb <kB> wall <m:ss>"; <out>/<M>.log;
#         <out>/inputs.sha256 (raw files and the copies: equal hashes show that nothing was edited).
set -u
W=/home/dombarker/project-offloads/future-version-20261111
RAW=$1; NS=$2; D=$3
B=$W/x3/aeneas-src/backends/lean
TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
test ! -e $D || { echo "exists: $D"; exit 2; }
mkdir -p $D/src/$NS $D/out/$NS
cp $RAW/Types.lean $RAW/Funs.lean $D/src/$NS/
[ -f $RAW/TypesExternal_Template.lean ] && cp $RAW/TypesExternal_Template.lean $D/src/$NS/TypesExternal.lean
cp $RAW/FunsExternal_Template.lean $D/src/$NS/FunsExternal.lean
sha256sum $RAW/*.lean $D/src/$NS/*.lean > $D/inputs.sha256
LP=$D/out:$B/.lake/build/lib/lean
for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
$TCD/bin/lean --version > $D/lean-version.txt 2>&1
for M in TypesExternal Types FunsExternal Funs; do
  [ -f $D/src/$NS/$M.lean ] || continue
  /usr/bin/time -v -o $D/$M.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 2400 $TCD/bin/lean -j1 -M7000 \
    -DElab.async=false -DmaxErrors=100000 -R $D/src -o $D/out/$NS/$M.olean $D/src/$NS/$M.lean > $D/$M.log 2>&1
  rc=$?
  echo "$M $rc errors $(grep -c ': error' $D/$M.log) peak_kb $(grep 'Maximum resident' $D/$M.time | awk '{print $NF}') wall $(grep 'Elapsed' $D/$M.time | awk '{print $NF}')" >> $D/exit.txt
done
