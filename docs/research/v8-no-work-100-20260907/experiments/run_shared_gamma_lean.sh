#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(shasum -a 256 "$ex/AffinePrimal.lean" | cut -d' ' -f1)" == 5853394263e336cc2cddfd860ca7e157acb207b08deed3fe20669946ae62718d && "$(shasum -a 256 "$ex/AffinePrimal.olean" | cut -d' ' -f1)" == e788b85338eb0a5e8e388cad6cbe5309f3475181439f46d3889bdfea22de1f74 ]] || exit 2
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
[[ "$(shasum -a 256 "$ex/SemanticCarry.lean" | cut -d' ' -f1)" == 717b4bfcef6e1517780f1052d6961c7c0c02809c247606c92262b30916177d54 && "$(shasum -a 256 "$ex/SemanticCarry.olean" | cut -d' ' -f1)" == f90b84321f2ca2620a6963fa362af7521485bf0ced54109e084f58c05ce13ea2 ]] || exit 2
[[ "$(shasum -a 256 "$ex/QmCrossRange.lean" | cut -d' ' -f1)" == cb06024066b66778a8e3de356871d4766ce2d6b17a7b698890195f8a9329f409 ]] || exit 2
cd "$cache"
{
 shasum -a 256 "$ex/SharedGammaDots.lean" "$ex/SemanticCarry.lean" "$ex/SemanticCarry.olean" "$ex/QmCrossRange.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 # The predecessor's olean was absent. Compile this focused dependency once;
 # there is no package/dependency rebuild or changed mathematical statement.
 if [[ ! -e "$ex/QmCrossRange.olean" ]];then
  /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/QmCrossRange.olean" "$1/QmCrossRange.lean"' _ "$ex"
 fi
 [[ "$(shasum -a 256 "$ex/QmCrossRange.olean" | cut -d' ' -f1)" == b305936b5137a85f5015d363bcb0d416a2de9e4da2ba3d4d4453ec589718f064 ]] || exit 2
 shasum -a 256 "$ex/QmCrossRange.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/SharedGammaDots.olean" "$1/SharedGammaDots.lean"' _ "$ex"
 shasum -a 256 "$ex/SharedGammaDots.olean"
} 2>&1 | tee "$log"
