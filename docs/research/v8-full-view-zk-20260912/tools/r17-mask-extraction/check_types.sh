#!/usr/bin/env bash
set -euo pipefail
# First actual generated dependency, using only its required cached imports.
# Invoke in MemoryHigh=4G, MemoryMax=6G, MemorySwapMax=0 scope.
raw=${1:?pinned generated Types.lean}
task=${2:?fresh task directory}
test ! -e "$task"
test "$(sha256sum "$raw" | cut -d' ' -f1)" = 51e47fa8908d7776913478ae49e944d4de16777d9966fc33eadc50935c0e3554
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
packages=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
test "$(git -C "$packages/.lake/packages/mathlib" rev-parse HEAD)" = 81a5d257c8e410db227a6665ed08f64fea08e997
mkdir -p "$task/AspisR17MaskSource"
# No declaration/type/body changes; avoid importing unrelated Aeneas tactics.
sed 's/^import Aeneas$/import Aeneas.Std.Scalar.Core/' "$raw" > "$task/AspisR17MaskSource/Types.lean"
base="$runtime/.lake/build/lib/lean"
count=0
for package in "$packages"/.lake/packages/*/.lake/build/lib/lean; do
  base="$package:$base"
  count=$((count+1))
done
test "$count" = 8
export LEAN_PATH="$task:$base"
cd "$task"
# New concrete-runtime target: import budget selected before first attempt.
/usr/bin/time -v "$lean" -j1 -M3200 -o AspisR17MaskSource/Types.olean AspisR17MaskSource/Types.lean
