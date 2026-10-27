"""Private retained object links preserving resolution order, excluding h5 rebuilds."""
from pathlib import Path
import json,sys
H=Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026');P=H/'runjoin24-lean'
e=json.loads((P/'J.json').read_text());roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
exclude=set(json.load(sys.stdin));out=P/'objects';rows=[]
for root in roots:
 if root==out or not root.is_dir():continue
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(root);module=str(rel).split('.olean')[0].split('.ilean')[0]
  if module in exclude:continue
  q=out/rel
  if q.exists() or q.is_symlink():continue
  q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p.resolve())
  rows.append(dict(path=str(q),retained=str(p.resolve())))
print(json.dumps(dict(overwritten=[],excluded_h5=sorted(exclude),links=rows),indent=2))
