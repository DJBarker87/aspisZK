#!/bin/sh
set -eu
cd /home/dombarker/project-offloads/codex-cx-prover-commit52-20261022/build
[ ! -e launched.txt ] || { echo 'Cold build already launched'; exit 65; }
exec 9>/tmp/aspis-r0-lean.lock
flock 9
python3 - <<'PY'
from pathlib import Path
total = 0
for p in Path('/sys/fs/cgroup').rglob('memory.max'):
    try:
        v = p.read_text().strip()
        if v != 'max' and (p.parent / 'cgroup.procs').read_text().strip():
            total += int(v)
    except (PermissionError, FileNotFoundError, ProcessLookupError):
        pass
print('Populated reservation bytes:', total, 'additional:', 8 * 1024**3, flush=True)
assert total + 8 * 1024**3 <= 55 * 1024**3
PY
date -u > launched.txt
systemd-run --user --scope --unit=aspis-terminal-cone-build-52-1 --quiet \
  -p MemoryHigh=6G -p MemoryMax=8G -p MemorySwapMax=0 -p TasksMax=64 \
  /usr/bin/time -v -o BUILD-52-1.time python3 -u cold-build.py
