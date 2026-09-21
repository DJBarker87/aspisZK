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
  AspisV8R17/UnsignedCM31Cross) ;;
  AspisV8R17/UnsignedReducerOps) ;;
  AspisV8R17/UnsignedReducerExecution) ;;
  AspisV8R17/UnsignedLiteralSupport) ;;
  AspisV8R17/GeneratedReducerExpanded) ;;
  AspisV8R17/GeneratedM31Mul) ;;
  AspisV8R17/GeneratedM31Sub) ;;
  AspisV8R17/GeneratedCM31Mul) ;;
  AspisV8R17/GeneratedCM31Normalized) ;;
  AspisV8R17/GeneratedM31Add) ;;
  AspisV8R17/GeneratedCM31Square) ;;
  AspisV8R17/GeneratedCM31SquareNormalized) ;;
  AspisV8R17/HalfRotateNat) ;;
  AspisV8R17/SignedShiftSlice) ;;
  AspisV8R17/SignedLiteralSupport) ;;
  AspisV8R17/GeneratedM31Half) ;;
  AspisV8R17/GeneratedCM31Linear) ;;
  AspisV8R17/GeneratedQM31Scalar) ;;
  AspisV8R17/GeneratedMulByR) ;;
  AspisV8R17/GeneratedQM31Products) ;;
  AspisV8R17/GeneratedQM31Linear) ;;
  AspisV8R17/QM31WordFormulas|AspisV8R17/QM31WordResidues) ;;
  AspisV8R17/QuadraticTowerOperations) ;;
  AspisV8R17/RawReducerNat|AspisV8R17/RawReducer) ;;
  *) exit 2 ;;
esac
if [[ "$target" == AspisV8R17/UnsignedLiteralSupport || "$target" == AspisV8R17/GeneratedReducerExpanded ]]; then
  python3 "$task/check_r17_generated_reducer.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --literals "$task/AspisV8R17/UnsignedLiteralSupport.lean" \
    --generated "$task/AspisV8R17/GeneratedReducerExpanded.lean"
fi
if [[ "$target" == AspisV8R17/GeneratedM31Mul || "$target" == AspisV8R17/GeneratedM31Sub || "$target" == AspisV8R17/GeneratedCM31Mul || "$target" == AspisV8R17/GeneratedCM31Normalized || "$target" == AspisV8R17/GeneratedM31Add || "$target" == AspisV8R17/GeneratedCM31Square || "$target" == AspisV8R17/GeneratedCM31SquareNormalized ]]; then
  extra_checks=()
  if [[ "$target" != AspisV8R17/GeneratedM31Mul ]]; then
    extra_checks+=(--m31-sub "$task/AspisV8R17/GeneratedM31Sub.lean")
  fi
  if [[ "$target" == AspisV8R17/GeneratedCM31Mul || "$target" == AspisV8R17/GeneratedCM31Normalized || "$target" == AspisV8R17/GeneratedCM31SquareNormalized ]]; then
    extra_checks+=(--cm31-mul "$task/AspisV8R17/GeneratedCM31Mul.lean")
  fi
  if [[ "$target" == AspisV8R17/GeneratedM31Add || "$target" == AspisV8R17/GeneratedCM31Square || "$target" == AspisV8R17/GeneratedCM31SquareNormalized ]]; then
    extra_checks+=(--m31-add "$task/AspisV8R17/GeneratedM31Add.lean")
  fi
  if [[ "$target" == AspisV8R17/GeneratedCM31Square || "$target" == AspisV8R17/GeneratedCM31SquareNormalized ]]; then
    extra_checks+=(--cm31-square "$task/AspisV8R17/GeneratedCM31Square.lean")
  fi
  python3 "$task/check_r17_generated_reducer.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --literals "$task/AspisV8R17/UnsignedLiteralSupport.lean" \
    --generated "$task/AspisV8R17/GeneratedReducerExpanded.lean" \
    --m31-mul "$task/AspisV8R17/GeneratedM31Mul.lean" "${extra_checks[@]}"
fi
if [[ "$target" == AspisV8R17/UnsignedCoreSlice || "$target" == AspisV8R17/UnsignedCM31Cross || "$target" == AspisV8R17/UnsignedReducerOps || "$target" == AspisV8R17/UnsignedReducerExecution ]]; then
  python3 "$task/check_r17_unsigned_slice.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --slice "$task/AspisV8R17/UnsignedCoreSlice.lean"
fi
if [[ "$target" == AspisV8R17/UnsignedCM31Cross || "$target" == AspisV8R17/UnsignedReducerOps || "$target" == AspisV8R17/UnsignedReducerExecution ]]; then
  python3 "$task/check_r17_unsigned_slice.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --slice "$task/AspisV8R17/UnsignedCM31Cross.lean" --cross
  python3 "$task/check_r17_field_slice.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --slice "$task/AspisV8R17/CurrentFieldSlice.lean" --cross-fragment "$task/AspisV8R17/UnsignedCM31Cross.lean"
fi
if [[ "$target" == AspisV8R17/UnsignedReducerOps || "$target" == AspisV8R17/UnsignedReducerExecution ]]; then
  python3 "$task/check_r17_unsigned_slice.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --slice "$task/AspisV8R17/UnsignedReducerOps.lean" --reducer
fi
if [[ "$target" == AspisV8R17/SignedShiftSlice ]]; then
  python3 "$task/check_r17_unsigned_slice.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --slice "$task/AspisV8R17/SignedShiftSlice.lean" --signed
fi
if [[ "$target" == AspisV8R17/SignedLiteralSupport || "$target" == AspisV8R17/GeneratedM31Half ]]; then
  half_args=()
  if [[ "$target" == AspisV8R17/GeneratedM31Half ]]; then
    half_args+=(--stage "$stage/V7Tag73CurrentHelpersOpaque" --generated "$task/AspisV8R17/GeneratedM31Half.lean")
  fi
  python3 "$task/check_r17_half.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --literals "$task/AspisV8R17/SignedLiteralSupport.lean" "${half_args[@]}"
fi
if [[ "$target" == AspisV8R17/GeneratedCM31Linear ]]; then
  python3 "$task/check_r17_generated_reducer.py" --runtime "$runtime/Aeneas/Std/Scalar" \
    --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --literals "$task/AspisV8R17/UnsignedLiteralSupport.lean" \
    --generated "$task/AspisV8R17/GeneratedReducerExpanded.lean" \
    --m31-add "$task/AspisV8R17/GeneratedM31Add.lean" \
    --m31-sub "$task/AspisV8R17/GeneratedM31Sub.lean" \
    --cm31-linear "$task/AspisV8R17/GeneratedCM31Linear.lean"
fi
if [[ "$target" == AspisV8R17/GeneratedQM31Scalar ]]; then
  python3 "$task/check_r17_qm31.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --scalar "$task/AspisV8R17/GeneratedQM31Scalar.lean"
fi
if [[ "$target" == AspisV8R17/GeneratedMulByR ]]; then
  python3 "$task/check_r17_qm31.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --scalar "$task/AspisV8R17/GeneratedQM31Scalar.lean" \
    --mul-by-r "$task/AspisV8R17/GeneratedMulByR.lean"
fi
if [[ "$target" == AspisV8R17/GeneratedQM31Products ]]; then
  python3 "$task/check_r17_qm31.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --scalar "$task/AspisV8R17/GeneratedQM31Scalar.lean" \
    --mul-by-r "$task/AspisV8R17/GeneratedMulByR.lean" \
    --products "$task/AspisV8R17/GeneratedQM31Products.lean"
fi
if [[ "$target" == AspisV8R17/GeneratedQM31Linear ]]; then
  python3 "$task/check_r17_qm31.py" --stage "$stage/V7Tag73CurrentHelpersOpaque" \
    --scalar "$task/AspisV8R17/GeneratedQM31Scalar.lean" \
    --mul-by-r "$task/AspisV8R17/GeneratedMulByR.lean" \
    --products "$task/AspisV8R17/GeneratedQM31Products.lean" \
    --linear "$task/AspisV8R17/GeneratedQM31Linear.lean"
fi
cd "$runtime"
test ! -L "$task/$target.olean"
exec /usr/bin/time -v "$lean" -j1 -M1800 -R "$task" \
  -o "$task/$target.olean" "$task/$target.lean"
