#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 1 && ! -e "$1" ]] || exit 2
readonly log="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
cd "$cache"
{
 shasum -a 256 "$ex/JoinedInverse.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env /usr/bin/time -l lean -M7000 -R "$ex" -o "$ex/JoinedInverse.olean" "$ex/JoinedInverse.lean"
 shasum -a 256 "$ex/JoinedInverse.olean"
} 2>&1 | tee "$log"
