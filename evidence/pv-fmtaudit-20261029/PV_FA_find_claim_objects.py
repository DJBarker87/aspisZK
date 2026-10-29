from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');B=H.parent;rows=json.loads((H/'credited-row-input.json').read_text());roots=[]
for job in B.glob('codex-pv-*'):
 for d in ['objects','lean-objects','lean-objects-R1Z','lean/objects','lean-objects/objects']:
  if(job/d).is_dir():roots.append(job/d)
for job in B.glob('codex-cx-*'):
 for d in ['objects','lean-objects']:
  if(job/d).is_dir():roots.append(job/d)
out=[]
for row in rows:
 t=row.get('closure_theorem');matches=[]
 if t:
  mod=t.rsplit('.',1)[0]
  for r in roots:
   p=r/(mod.replace('.','/')+'.olean')
   if p.exists():matches.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),root=str(r)))
 out.append(dict(id=row['id'],theorem=t,objects=matches))
(H/'claim-object-locations.json').write_text(json.dumps(out,indent=1));print('found',[(x['id'],len(x['objects']))for x in out]);print('roots searched',len(roots))
