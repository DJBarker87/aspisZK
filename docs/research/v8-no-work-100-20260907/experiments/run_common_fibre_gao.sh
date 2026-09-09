#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly lake_cache=/Users/dominic/ZK/AspisFormal
readonly decoder_cache=/tmp/aspis-v8-gao-lean.9dslpv
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
check(){ [[ "$(shasum -a 256 "$1" | cut -d' ' -f1)" == "$2" ]] || exit 2; }
check "$ex/GaoRecovery.lean" 4b508fc84e68b920f83512a5652002cc051bbad5ee13955c8099d0f5dfbfa1b0
check "$ex/GaoC1Recovery.lean" 1a7d4a33838f0cc2d865eced79ae10c92ef7256ea9873d79498261dd6095119e
check "$ex/CircleLaurentRecovery.lean" f35183b9c7461f2b6e8cc4e561233eb6817225914a93c7e4ff9b71b696b7ef94
check "$decoder_cache/GaoRecovery.olean" 5621ac83140c560cea5753ab46cdf5118d44a32736de4fa6ad87033d2d617810
check "$decoder_cache/CircleLaurentRecovery.olean" 959be50e0b3602c36c4bb38fe459d5a067fa7a034cbbe276f6605e919f2c93fe
[[ "$(git -C "$lake_cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
cd "$lake_cache"
{
  git -C "$ex" rev-parse HEAD
  /Users/dominic/.elan/bin/lake env lean --version
  shasum -a 256 "$ex/CommonFibreGaoRecovery.lean" "$ex/GaoC1Recovery.lean" "$ex/GaoRecovery.lean" "$ex/CircleLaurentRecovery.lean" "$decoder_cache/GaoRecovery.olean" "$decoder_cache/CircleLaurentRecovery.olean" "$lake_cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
  if [[ ! -e "$decoder_cache/GaoC1Recovery.olean" ]]; then
    echo 'Missing cached coefficient leaf: exporting once; no dependency replay.'
    /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$2" -o "$1/GaoC1Recovery.olean" "$2/GaoC1Recovery.lean"' _ "$decoder_cache" "$ex"
  fi
  check "$decoder_cache/GaoC1Recovery.olean" 0b8910e26e6be9962f6a00d20aee7c9f217b42cd990a61d1ca15da7dfe3564a9
  shasum -a 256 "$decoder_cache/GaoC1Recovery.olean"
  echo 'COMMAND: lake env [pinned LEAN_PATH] /usr/bin/time -l lean -M7000 -R EXPERIMENTS -o EXPERIMENTS/CommonFibreGaoRecovery.olean EXPERIMENTS/CommonFibreGaoRecovery.lean'
  status=0
  /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$2" -o "$2/CommonFibreGaoRecovery.olean" "$2/CommonFibreGaoRecovery.lean"' _ "$decoder_cache" "$ex" || status=$?
  echo "LEAN_EXIT=$status"
  [[ $status == 0 ]] || exit "$status"
  shasum -a 256 "$ex/CommonFibreGaoRecovery.olean"
} 2>&1 | tee "$log"
