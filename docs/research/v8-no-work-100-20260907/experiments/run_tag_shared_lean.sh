#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly target="$1" log="$2"
case "$target" in CopyTagSplit|CopyTagShared|CopyTagSums) ;; *) exit 2;; esac
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
python3 "$ex/generate_tag_shared.py" --check
# Import provenance is checked against the retained leaf source/olean evidence.
python3 - "$ex" "$target" <<'PY'
import sys,json,hashlib
from pathlib import Path
ex=Path(sys.argv[1]); target=sys.argv[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
if target=='CopyTagSums':
    row=json.loads((ex.parent/'scatter-performance-evidence.json').read_text())['lean']['leaves'][0]
    assert sha(ex/'CopyScatterNodes.lean')==row['source_sha256']
    assert sha(ex/'CopyScatterNodes.olean')==row['olean_sha256']
if target=='CopyTagShared':
    log=(ex/'tag-shared-split-cache.log').read_text()
    assert sha(ex/'CopyTagSplit.lean') in log and sha(ex/'CopyTagSplit.olean') in log
PY
cd "$cache"
{
 shasum -a 256 "$ex/$target.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/$2.olean" "$1/$2.lean"' _ "$ex" "$target"
 shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
