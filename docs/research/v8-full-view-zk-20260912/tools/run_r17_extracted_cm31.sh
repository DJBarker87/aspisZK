#!/usr/bin/env bash
set -euo pipefail

# Run only inside a caller-supplied bounded systemd scope on the cached host.
task=${1:?task-owned workspace required}
stage=/home/dombarker/project-offloads/aspis-v7-aeneas-source-unblock-20260830/staged-current-normalized-statement-owned-twohelpers-r19
runtime=/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/aeneas-full/backends/lean
packages=/home/dombarker/project-offloads/ZK-v7-one-tx-formal-consolidation-20260828/AspisFormal
lean=/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean
test -d "$task/AspisV8R17"
test "$(git -C "$packages/.lake/packages/mathlib" rev-parse HEAD)" = 81a5d257c8e410db227a6665ed08f64fea08e997
test "$(sha256sum "$stage/V7Tag73CurrentHelpersOpaque/FunsChunk04.lean" | cut -d' ' -f1)" = e79e0726e1a58ebfe3701b83f4339ca52b042e46cae833d573df3190c4bd0c21
base="$runtime/.lake/build/lib/lean"
count=0
for package in "$packages"/.lake/packages/*/.lake/build/lib/lean; do
  test -d "$package"
  base="$package:$base"
  count=$((count+1))
done
test "$count" = 8
export LEAN_PATH="$task:$stage:$base"
python3 "$task/check_r17_field_slice.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
  --slice "$task/AspisV8R17/CurrentFieldSlice.lean" --self-test
target=${2:-AspisV8R17/CurrentFieldSlice}
case "$target" in
  AspisV8R17/CurrentFieldSlice|AspisV8R17/ExtractedCM31Operands|AspisV8R17/ScalarImportProbe) ;;
  AspisV8R17/UnsignedCoreSlice) ;;
  *) exit 2 ;;
esac
if [[ "$target" == AspisV8R17/UnsignedCoreSlice ]]; then
  python3 "$task/check_r17_unsigned_slice.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --slice "$task/$target.lean"
fi
cd "$runtime"
test ! -L "$task/$target.olean"
exec /usr/bin/time -v "$lean" -j1 -M1800 -R "$task" \
  -o "$task/$target.olean" "$task/$target.lean"
