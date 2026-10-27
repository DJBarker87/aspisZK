#!/usr/bin/env python3
"""Delete only this task's rebuildable Cargo targets; retain source/bin/evidence."""
from pathlib import Path
import shutil,json,time,hashlib
B=Path('/home/dombarker/project-offloads/codex-pv-dudect-20261027')
t=time.monotonic();deleted=[]
for name in ['harness-target','candidate-target']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():shutil.rmtree(p);deleted.append(str(p))
rec=dict(target='remove job-owned harness-target and candidate-target only',exit_status=0,wall_seconds=time.monotonic()-t,source_revision='73070ddd512bc4e79edfc0db714fb64dc74e87b8',print_axioms='N/A: file cleanup only',deleted=deleted,targets_absent=all(not (B/n).exists() for n in ['harness-target','candidate-target']),retained_binary_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (B/'bin').iterdir()},quiet_marker_written=False,keys_created_or_deleted=False)
(B/'cleanup.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
