#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
python3 - "$H" <<'PY'
import json,sys
from pathlib import Path
h=Path(sys.argv[1])
for name in ['trace-main','trace-control']:
 p=json.loads((h/f'plan-{name}.json').read_text());r=[json.loads(x) for x in (h/f'sweep/{name}/sweep.jsonl').read_text().splitlines()]
 assert len(r)==len(p['runs']) and all(x['exit_status']==0 and x['outcome']=='accepted' for x in r)
PY
python3 "$H/harness/reservation.py" "$H/reservation-analysis.json"
systemd-run --user --scope -q -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 python3 "$H/harness/capped.py" "$H/receipts/audit-main" "time expected in candidate ELF CFG longest-arm and exact-input register aggregation for 74 replays" -- bash "$H/harness/run_audit.sh" "$H/analysis" "$H"/traces/trace-main/* "$H"/traces/trace-control/*
bash "$H/harness/map-analysis.sh" "$H/analysis"
python3 "$H/harness/runs_meta.py" "$H/analysis/runs.json" "$H/sweep/trace-main/sweep.jsonl" "$H/sweep/trace-control/sweep.jsonl"
