#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly cache=/Users/dominic/ZK/AspisFormal
readonly repo="$(git -C "$ex" rev-parse --show-toplevel)"
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
readonly core_src=87238dadc0a8925ccbbbd337e4eee71f1f56acad6c65626b1b70d9bd58095efd
readonly value_src=2b3ebca0fe5ec333c0471336fac8df41c869cc8b04f1eced02f5a1822c8b8d3e
for root in "$repo/AspisFormal" "$cache"; do
  check "$root/AspisFormal/ArithmetizationCore.lean" "$core_src"
  check "$root/AspisFormal/ValueConservation.lean" "$value_src"
done
check "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" 6ab5f3738e8018b86409fd1ec394527d1e6eded5816817f11385529e0c579300
check "$cache/.lake/build/lib/lean/AspisFormal/ValueConservation.olean" 332f6aca6ab9b69eccb050d31895abf1f51ccfc9c97fa9015ab196bee634eaa1
check "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib.olean" 9c5bf984a8c4ed7c7854d68673a37a3847ff24783554f451920d4ff95d68b97e
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
cd "$cache"
{
  git -C "$repo" rev-parse HEAD
  shasum -a 256 "$ex/SelectedPaymentRecovery.lean" \
    "$cache/AspisFormal/ArithmetizationCore.lean" \
    "$cache/.lake/build/lib/lean/AspisFormal/ArithmetizationCore.olean" \
    "$cache/AspisFormal/ValueConservation.lean" \
    "$cache/.lake/build/lib/lean/AspisFormal/ValueConservation.olean"
  /Users/dominic/.elan/bin/lake env lean --version
  /Users/dominic/.elan/bin/lake env bash -c '
    export LEAN_PATH="$1:$LEAN_PATH"
    /usr/bin/time -l lean -M7000 -R "$1" -o "$1/SelectedPaymentRecovery.olean" "$1/SelectedPaymentRecovery.lean"
    result=$?
    echo "LEAN_EXIT=$result"
    exit "$result"
  ' _ "$ex"
  shasum -a 256 "$ex/SelectedPaymentRecovery.olean"
} 2>&1 | tee "$log"
