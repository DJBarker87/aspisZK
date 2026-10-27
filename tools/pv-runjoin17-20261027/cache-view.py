"""Compose private read-only links to existing valid R1Z objects; no compilation."""
from pathlib import Path
import json
H=Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026');P=H/'runjoin17-lean';out=P/'objects/R1Z'
e=json.loads((P/'J.json').read_text());roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
rows=[]
for root in roots:
 if root==P/'objects':continue
 src=root/'R1Z'
 if not src.is_dir():continue
 for p in sorted(src.rglob('*.olean')):
  if not p.is_file():continue
  q=out/p.relative_to(src)
  if q.exists() or q.is_symlink():continue
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve())
  rows.append(dict(module='R1Z.'+'.'.join(p.relative_to(src).with_suffix('').parts),private_path=str(q),retained_object=str(p.resolve()),bytes=p.stat().st_size,shared_written=False))
print(json.dumps(dict(existing_environment_precedence_preserved=True,overwritten_paths=[],links=rows),indent=2))
