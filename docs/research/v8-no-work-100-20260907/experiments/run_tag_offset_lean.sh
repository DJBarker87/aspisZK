#!/usr/bin/env bash
set -euo pipefail
readonly ex="$(cd "$(dirname "$0")" && pwd)" cache=/Users/dominic/ZK/AspisFormal
[[ $# == 2 && ! -e "$2" ]] || exit 2
readonly target="$1" log="$2"
case "$target" in CopyTagOffsetModel|CopyTagOffsetPlans) ;; *) exit 2;; esac
[[ "$(git -C "$cache/.lake/packages/mathlib" rev-parse HEAD)" == 81a5d257c8e410db227a6665ed08f64fea08e997 ]] || exit 2
python3 "$ex/generate_tag_offsets.py" --check
python3 - "$ex" "$target" <<'PY'
import sys,json,hashlib
from pathlib import Path
ex=Path(sys.argv[1])
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
row=json.loads((ex.parent/'tag-shared-results.json').read_text())['lean'][0]
assert sha(ex/'CopyTagSplit.lean')==row['source_sha256']
assert sha(ex/'CopyTagSplit.olean')==row['olean_sha256']
if sys.argv[2]=='CopyTagOffsetPlans':
    log=(ex/'tag-offset-model-lean.log').read_text()
    assert sha(ex/'CopyTagOffsetModel.lean') in log and sha(ex/'CopyTagOffsetModel.olean') in log
PY
cd "$cache"
{
 shasum -a 256 "$ex/$target.lean" "$cache/.lake/packages/mathlib/.lake/build/lib/lean/Mathlib/Tactic.olean"
 /Users/dominic/.elan/bin/lake env bash -c 'export LEAN_PATH="$1:$LEAN_PATH"; /usr/bin/time -l lean -M7000 -R "$1" -o "$1/$2.olean" "$1/$2.lean"' _ "$ex" "$target"
 shasum -a 256 "$ex/$target.olean"
} 2>&1 | tee "$log"
