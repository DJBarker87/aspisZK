#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly cache=/Users/dominic/ZK/AspisFormal
[[ $# == 1 && ! -e "$1" ]] || exit 2
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
readonly log="$1"
cd "$cache"
{
 shasum -a 256 "$ex/CopyTagSplit.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env /usr/bin/time -l lean -M7000 "$ex/CopyTagSplit.lean"
} 2>&1 | tee "$log"
