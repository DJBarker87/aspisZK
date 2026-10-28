from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');O=D/'objects'
x=json.loads((D/'preflight.json').read_text());rows=[]
for r in x['project']:
 if r['module']=='R1Z.PV_RDEA_CloneExecution':continue
 p=Path(r['object']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256']
 q=O/(r['module'].replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if not q.exists():q.symlink_to(p)
 for suffix in ['.private','.server']:
  a=Path(str(p)+suffix);b=Path(str(q)+suffix)
  if a.exists() and not b.exists():b.symlink_to(a)
 rows.append(dict(module=r['module'],path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
(D/'cache.json').write_text(json.dumps(rows,indent=2)+'\n');print('linked verified inherited cohort',len(rows))
