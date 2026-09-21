#!/usr/bin/env bash
set -euo pipefail
# Separate proof cache: DO NOT add the old declaration-projection workspace.
# Invoke one target per zero-swap, 4G-high/6G-max systemd scope.
task=${1:?full-runtime stage}
target=${2:?focused target}
case "$target" in UnsignedCoreSlice|UnsignedCM31Cross|UnsignedReducerOps|FullRuntimeWrapping) ;; *) exit 2 ;; esac
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
packages=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
test "$(git -C "$packages/.lake/packages/mathlib" rev-parse HEAD)" = 81a5d257c8e410db227a6665ed08f64fea08e997
for entry in \
  'Add:6b20fc30c237b8bfac99f9cd1e45f8150edcaabe4c62fdca5b0ceeb3a4a9b1a4' \
  'Mul:4d6f81c964cfa9b3b6808bc6d2703d3f2dbde5c70ce3ae76541905304802beb8' \
  'Sub:a07d2e801092fe35e9e0fd376a9723a2e1486467ff08769faae7644f55ce898e'; do
  test "$(sha256sum "$runtime/Aeneas/Std/Scalar/WrappingOps/${entry%%:*}.lean" | cut -d' ' -f1)" = "${entry#*:}"
done
base="$runtime/.lake/build/lib/lean"
count=0
for package in "$packages"/.lake/packages/*/.lake/build/lib/lean; do
  base="$package:$base"
  count=$((count+1))
done
test "$count" = 8
export LEAN_PATH="$task:$base"
cd "$task"
test ! -L "AspisV8R17/$target.olean"
exec /usr/bin/time -v /home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean \
  -j1 -M3200 -o "AspisV8R17/$target.olean" "AspisV8R17/$target.lean"
