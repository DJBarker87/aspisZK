from pathlib import Path
import json,hashlib,os
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028');O=D/'actual-objects'
pf=json.loads((D/'preflight.json').read_text());authority=json.loads((D.parent/'codex-pv-rdb1-20261028/external-object-manifest.json').read_text());loaded={x['module']:x for x in pf['checks']};rows=[]
for entry in authority:
 row=loaded[entry['module']];p=Path(row['path']);expected=entry['object_sha256'];actual=hashlib.sha256(p.read_bytes()).hexdigest();assert actual==expected,(entry['module'],actual,expected)
 out=O/(entry['module'].replace('.','/')+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 if out.exists() or out.is_symlink():assert out.is_file() and hashlib.sha256(out.read_bytes()).hexdigest()==expected
 else:out.symlink_to(p)
 # Optional split companion artifacts, if the selected object has any.
 companions=[]
 for suffix in ['.private','.server']:
  q=Path(str(p)+suffix)
  if q.is_file():
   dest=Path(str(out)+suffix)
   if not dest.exists():dest.symlink_to(q)
   assert hashlib.sha256(dest.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()
   companions.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
 rows.append(dict(module=entry['module'],path=str(out),target=str(p),sha256=actual,companions=companions))
(D/'private-cache-preflight.json').write_text(json.dumps(dict(ok=True,count=len(rows),rows=rows,reason='Private run2 prefix lacked the shared cache first. Pinned external objects are linked read-only into this job only, avoiding dangling legacy aliases without modifying them.'),indent=2)+'\n');print('verified external links',len(rows))
