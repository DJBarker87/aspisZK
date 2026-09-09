#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 2 && ! -e "$2" && ( "$1" == CircleNorm || "$1" == CircleNormTables ) ]] || exit 2
readonly target="$1" log="$(cd "$(dirname "$2")" && pwd)/$(basename "$2")"
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
# Reuse the unchanged, already-audited ChordNorm source/olean pair.
[[ "$(shasum -a 256 "$ex/ChordNorm.olean" | cut -d' ' -f1)" == "$(python3 -c 'import json,sys;print(json.load(open(sys.argv[1]))["lean"]["olean_sha256"])' "$ex/../chord-norm-results.json")" ]] || exit 2
cd "$cache"
{
 shasum -a 256 "$ex/$target.lean" "$ex/ChordNorm.lean" "$ex/ChordNorm.olean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env /usr/bin/time -l env LEAN_PATH="$ex:$(/Users/dominic/.elan/bin/lake env printenv LEAN_PATH)" lean -M7000 -R "$ex" -o "$ex/$target.olean" "$ex/$target.lean"
 shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
