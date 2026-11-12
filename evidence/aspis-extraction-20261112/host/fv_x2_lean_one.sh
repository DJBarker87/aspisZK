#!/bin/bash
# X2: compile ONE Lean module of the Pool emission against the L187 release objects of the R1 bound layer, by reference
# (never written). The command of fv_frz_emit_lean_one.sh (Lean 4.32.0, -j1 -M7000, Elab.async=false); the timeout is
# the third argument (default 180 s, as there). Runs INSIDE the fv_slot.sh scope of fv_x2.sh.
# Usage: fv_x2_lean_one.sh <out-dir> <Module> [<timeout-seconds>]
set -u
SYS=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
D=$1; M=$2; TO=${3:-180}
mkdir -p $D/lean-out
sha256sum $D/lean-src/$M.lean
T=$D/lean-out/.partial.$$.$M.olean
env PATH=/usr/bin:/bin LEAN_SYSROOT=$SYS LEAN_PATH=$D/lean-out:$L/objs:$L/base_ref \
  timeout $TO $SYS/bin/lean -j1 -M7000 -DElab.async=false -R $D/lean-src -o $T $D/lean-src/$M.lean
rc=$?
if [ $rc -eq 0 ] && [ -f $T ]; then mv -f $T $D/lean-out/$M.olean; elif [ -f $T ]; then mv -f $T $T.failed; fi
exit $rc
