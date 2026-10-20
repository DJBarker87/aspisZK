#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound3-20261020
A=$H/analysis
# Only composition is repeated: the sweep input artifact is now complete.
python3 - "$H" <<'PY'
import json,sys
from pathlib import Path
H=Path(sys.argv[1])
for ss in ['random-a','random-b']:
 rows=[json.loads(l) for l in (H/'sweep'/ss/'sweep.jsonl').read_text().splitlines()]
 assert len(rows)==300 and all(r.get('outcome')=='accepted' for r in rows)
PY
python3 "$H/harness/bound2.py" "$A" "$H/harness/rules.json" "$A" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" -- "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" "$H/sweep/targeted/sweep.jsonl" "$H/sweep/random-a/sweep.jsonl" "$H/sweep/random-b/sweep.jsonl" "$H/sweep/control/sweep.jsonl" "$H/sweep/fresh-control/sweep.jsonl"
python3 "$H/harness/make_deliverables.py" "$A" "$H/harness/rules.json" "$H/variants-measured.json" "$A"
python3 "$H/harness/check_results.py" "$H" "$A" "$H/validation.json"
