#!/usr/bin/env bash
# Focused leaves, not a package-wide replay. Reuses the verified Mathlib cache.
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)"
readonly cache=/Users/dominic/ZK/AspisFormal
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly target="$1" log="$2"
case "$target" in CopyScatterNodes|CopyScatterCells30|CopyScatterCells55|CopyScatterCells80|CopyScatterPlan) ;; *) exit 2;; esac
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
python3 "$ex/generate_copy_scatter.py" --check
cd "$cache"
{
 shasum -a 256 "$ex/$target.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/$2.olean" "$1/$2.lean"' _ "$ex" "$target"
 shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
