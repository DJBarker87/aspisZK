#!/usr/bin/env bash
set -euo pipefail
# Invoke inside a bounded zero-swap Linux scope; no dependency rebuilds.
task=${1:?task workspace}
raw=${2:?pinned generated Funs.lean}
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
packages=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
leaf="$task/AspisV8R17/MaskClosureWriteback.lean"
test ! -L "$task/AspisV8R17/MaskClosureWriteback.olean"
test "$(git -C "$packages/.lake/packages/mathlib" rev-parse HEAD)" = 81a5d257c8e410db227a6665ed08f64fea08e997
python3 "$task/check_closure.py" "$raw" "$leaf"
base="$runtime/.lake/build/lib/lean"
count=0
for package in "$packages"/.lake/packages/*/.lake/build/lib/lean; do
  base="$package:$base"
  count=$((count+1))
done
test "$count" = 8
export LEAN_PATH="$task:$base"
cd "$task"
/usr/bin/time -v "$lean" -j1 -M1800 -o AspisV8R17/MaskClosureWriteback.olean "$leaf"
