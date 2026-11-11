#!/bin/bash
# Runs INSIDE a scope (fv_scope64.sh). Compile ONE Aspis Lean module against the L187 release
# objects of the R1 bound layer, by reference (recipe from the soundness lead, 2026-11-11).
# Usage: fv_lean_one.sh <Module>      source: $W/lean-src/<Module>.lean   object: $W/lean-out/<Module>.olean
# Read-only inputs, never written: codex-cx-replay-l187-20261109/{objs,base_ref}. Toolchain 4.32.0 only.
set -u
W=/home/dombarker/project-offloads/future-version-20261111
SYS=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0
L=/home/dombarker/project-offloads/codex-cx-replay-l187-20261109
M=$1
mkdir -p $W/lean-out
sha256sum $W/lean-src/$M.lean
# The object is written under a temporary name and moved into place only on success, so a
# concurrent compile never reads a half-written object.
T=$W/lean-out/.partial.$$.$M.olean
env PATH=/usr/bin:/bin LEAN_SYSROOT=$SYS LEAN_PATH=$W/lean-out:$L/objs:$L/base_ref \
  timeout 180 $SYS/bin/lean -j1 -M7000 -DElab.async=false -R $W/lean-src -o $T $W/lean-src/$M.lean
rc=$?
if [ $rc -eq 0 ] && [ -f $T ]; then mv -f $T $W/lean-out/$M.olean; else rm -f $T; fi
exit $rc
