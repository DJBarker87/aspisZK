#!/usr/bin/env bash
set -euo pipefail
# Each invocation compiles ONE focused target; caller supplies zero-swap scope.
task=${1:?staged task directory}
closure=${2:?compiled MaskClosureWriteback workspace}
target=${3:?Types, IteratorCompat, IteratorLaws, CollectorLaws, Funs, or AuditCaller}
case "$target" in Types|IteratorCompat|IteratorLaws|CollectorLaws|Funs|AuditCaller|AuditWorkspace|WorkspaceZero) ;; *) exit 2 ;; esac
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
packages=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
test "$(git -C "$packages/.lake/packages/mathlib" rev-parse HEAD)" = 81a5d257c8e410db227a6665ed08f64fea08e997
test "$(sha256sum "$closure/AspisV8R17/MaskClosureWriteback.lean" | cut -d' ' -f1)" = 953ea55acef72a5f414d54f3ac23ca1f194df891fea962bbfbda3de26d40ed65
for entry in \
  'Core/Ops.lean:f5d4a2e02ad41205d05a707ef345297194928a9340bc6e8cf03c349065c855d2' \
  'Core/Iter.lean:37e6d1901461e1df84f87a753ca3452eec4885e0779a12046630f5e26ea86985' \
  'SliceIter.lean:44d29a5d2cd24a85249c79313fb5a0beaa89a0aec09725c6ac2f75644b2f5e92' \
  'VecIter.lean:84a6fe24ce188a5340d55126c74e74e58d9f165346d89de6c63dc1c8f6cbac7f'; do
  test "$(sha256sum "$runtime/Aeneas/Std/${entry%%:*}" | cut -d' ' -f1)" = "${entry#*:}"
done
base="$runtime/.lake/build/lib/lean"
count=0
for package in "$packages"/.lake/packages/*/.lake/build/lib/lean; do
  base="$package:$base"
  count=$((count+1))
done
test "$count" = 8
export LEAN_PATH="$task:$closure:$base"
cd "$task"
test ! -L "AspisR17MaskSource/$target.olean"
/usr/bin/time -v "$lean" -j1 -M3200 -o "AspisR17MaskSource/$target.olean" "AspisR17MaskSource/$target.lean"
