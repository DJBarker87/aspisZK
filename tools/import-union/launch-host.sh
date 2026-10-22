#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-cx-import-union-20261022
# No shared launcher or lock is wrapped. Night-window reservation is checked.
python3 - <<'PY'
from pathlib import Path
import json, time
rows = []
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v = p.read_text().strip()
        if v != 'max' and (p.parent / 'cgroup.procs').read_text().strip():
            rows.append({'cgroup': str(p.parent), 'max_bytes': int(v)})
    except (PermissionError, FileNotFoundError, ProcessLookupError):
        pass
record = {'time_unix': time.time(), 'populated_scopes': rows, 'additional_bytes': 8*1024**3}
Path('evidence/reservation-'+str(time.time_ns())+'.json').write_text(json.dumps(record, indent=2)+'\n')
assert sum(r['max_bytes'] for r in rows)+8*1024**3 <= 55*1024**3, record
PY
exec systemd-run --user --scope --unit="aspis-import-union-$(date +%s)" --quiet \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  python3 -u host-build.py "$@"
