#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
[[ "$(shasum -a 256 "$ex/AffinePrimal.lean" | cut -d' ' -f1)" == 5853394263e336cc2cddfd860ca7e157acb207b08deed3fe20669946ae62718d && "$(shasum -a 256 "$ex/AffinePrimal.olean" | cut -d' ' -f1)" == e788b85338eb0a5e8e388cad6cbe5309f3475181439f46d3889bdfea22de1f74 ]] || exit 2
cd "$cache"
{
 shasum -a 256 "$ex/SemanticCarry.lean" "$ex/AffinePrimal.lean" "$ex/AffinePrimal.olean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/SemanticCarry.olean" "$1/SemanticCarry.lean"' _ "$ex"
 shasum -a 256 "$ex/SemanticCarry.olean"
} 2>&1 | tee "$log"
