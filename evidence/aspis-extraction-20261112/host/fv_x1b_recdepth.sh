#!/bin/bash
# X1b item M: the emitted TABLE_A and TABLE_B definitions (copied verbatim from a raw Funs.lean) compiled alone against
# the native library under several `maxRecDepth` values, to find the `-max-recdepth` emission flag at which they
# elaborate. A diagnostic only; the deliverable is the emission flag. Runs INSIDE one fv_slot.sh scope.
# Usage: fv_x1b_recdepth.sh <raw Funs.lean> <out dir> <depth>...
set -u
W=/home/dombarker/project-offloads/future-version-20261111
F=$1; D=$2; shift 2
B=$W/x3/aeneas-src/backends/lean; TCD=$HOME/.elan/toolchains/leanprover--lean4---v4.36.0-rc2
LP=$B/.lake/build/lib/lean; for p in $B/.lake/packages/*; do LP=$LP:$p/.lake/build/lib/lean; done
mkdir -p $D
for T in TABLE_A TABLE_B; do
  awk -v k="fast_domain::$T]" 'index($0, "/-- [aspis_r1_cost_probe::") == 1 && index($0, k) {p=1} p{print} p && /^$/{exit}' $F > $D/$T.body
  for N in "$@"; do
    { echo "import Aeneas"; echo "open Aeneas Aeneas.Std Result"; echo "set_option maxRecDepth $N"; echo "namespace AspisX1"; cat $D/$T.body; echo "end AspisX1"; } > $D/$T-$N.lean
    /usr/bin/time -v -o $D/$T-$N.time env PATH=/usr/bin:/bin LEAN_PATH=$LP timeout 1200 $TCD/bin/lean -j1 -M7000 -DElab.async=false $D/$T-$N.lean > $D/$T-$N.log 2>&1
    echo "$T maxRecDepth $N exit $? errors $(grep -c ': error' $D/$T-$N.log) peak_kb $(grep 'Maximum resident' $D/$T-$N.time | awk '{print $NF}') wall $(grep Elapsed $D/$T-$N.time | awk '{print $NF}')"
  done
done
