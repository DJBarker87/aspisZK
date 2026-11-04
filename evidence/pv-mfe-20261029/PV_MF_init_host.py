from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');P=D.parent/'codex-pv-mfd-20261029';C=D.parent/'codex-pv-mfc-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();inp=json.load(open(D/'rebuild-input.json'))
for m,v in inp['modules'].items():
 p=P/'sources'/(m.replace('.','/')+'.lean');assert sha(p)==v['sha256'];q=D/'sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
for p in (P/'objects').rglob('*.olean'):
 q=D/'objects'/p.relative_to(P/'objects');q.parent.mkdir(parents=True,exist_ok=True);q.symlink_to(p)
collisions=[]
for root in D.parent.glob('codex-*'):
 if root==D:continue
 for p in root.glob('lean-703*'):
  if p.name[5:].isdigit() and 70300<=int(p.name[5:])<=70399:collisions.append(str(p))
assert not collisions,collisions
(D/'id-collision-review.json').write_text(json.dumps(dict(range=[70300,70399],collisions=collisions),indent=2)+'\n')
print('sources',len(inp['modules']),'cache links',len(list((D/'objects').rglob('*.olean'))),'no collisions')
