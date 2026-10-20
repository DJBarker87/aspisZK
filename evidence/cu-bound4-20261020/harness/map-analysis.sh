#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound4-20261020
A=$1
python3 - "$A" <<'PY'
import json,sys
from pathlib import Path
A=Path(sys.argv[1])
for role in ['stage1','stage2','pool']:
 d=json.loads((A/f'{role}.json').read_text());ad=sorted(set([b['addr'] for b in d['branches']]+[l['header'] for l in d['loops']]))
 (A/f'addrs-{role}.json').write_text(json.dumps(ad))
PY
for role in stage1 stage2; do
python3 "$H/harness/map_lines.py" "$H/artifacts/verifier/linked.elf" "$H/artifacts/verifier-debuglines/linked.elf" "$A/addrs-$role.json" "$A/lines-$role.json"
done
# Pool is whole-file identical: its previous exact-address line map is reusable.
cp /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/analysis/main/lines-pool.json "$A/lines-pool.json"
cp /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/analysis/main/hdrlines-pool.json "$A/hdrlines-pool.json"
