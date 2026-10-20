#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
A=$H/analysis
cp "$A/bound.json" "$A/bound-before-canonical-cap-citations.json"
python3 "$H/harness/candidate_rules.py" "$H" "$A" "$H/harness/rules-rebased.json" "$H/harness/rules.json"
python3 "$H/harness/residual.py" "$A" "$A/runs.json" "$H/harness/rules.json" "$A"
python3 "$H/harness/bound2.py" "$A" "$H/harness/rules.json" "$A" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" -- "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" "$H/sweep/targeted/sweep.jsonl" "$H/sweep/random-a/sweep.jsonl" "$H/sweep/random-b/sweep.jsonl" "$H/sweep/control/sweep.jsonl"
python3 "$H/harness/make_deliverables.py" "$A" "$H/harness/rules.json" "$H/variants-measured.json" "$A"
python3 "$H/harness/new_path_audit.py" "$H"
python3 "$H/harness/validate_final.py" "$H"
python3 - "$H" <<'PY'
import json,sys
from pathlib import Path
h=Path(sys.argv[1]);a=json.loads((h/'analysis/bound-before-canonical-cap-citations.json').read_text());b=json.loads((h/'analysis/bound.json').read_text())
assert a==b,'Citation enrichment must not change any bound or sweep result'
(h/'canonical-cap-check.json').write_text(json.dumps(dict(source='c16e59e77',headers=['0xc3da0','0xc3e48'],bounds_unchanged=True,reason='fixed 22-opening / four-subslot scans; source lines and directly checked ELF counters'),indent=1)+'\n')
PY
