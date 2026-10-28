"""Copy pinned predecessor artifacts into the task cache; no Lean execution."""
from pathlib import Path
import json,shutil,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-reconcile-cache-20261028')
P=Path('/home/dombarker/project-offloads/codex-cx-l188-cache-20261028')
S=Path('/home/dombarker/project-offloads/codex-cx-sha453-cache-20261028')
plan=json.loads((B/'NDO_RETARGET_PLAN.json').read_text());mapping=json.loads((B/'NDO_NAME_MAP.json').read_text());affected={r['original'] for r in plan}
x=json.loads((P/'NDJ_CACHE_PINS.json').read_text());u={r['module']:r for r in x['objects'] if r['selection']=='union'};j={r['module']:r for r in x['objects'] if r['selection']=='joint'}
h=set()
def walk(m):
 if m in h:return
 h.add(m)
 for n in u[m]['imports']:walk(n)
walk('RPx_Deployed');rows=[]
for m,r in sorted({**{m:r for m,r in j.items() if m not in affected and m not in mapping},**{m:u[m] for m in h}}.items()):
 for a in r['artifacts']:
  p=Path(a['path']);rel=p.relative_to(P/('objects' if r['selection']=='union' else 'joint_objects'));q=B/'objects'/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==a['sha256'],str(q)
  else:shutil.copyfile(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==a['sha256'],str(q)
 rows.append(dict(module=m,sha256=r['sha256'],path=str(B/'objects'/(m.replace('.','/')+'.olean')),imports=r['imports']))
for name in ['S2W_run_host.py','S2W_lean_host_agg16.py','S2W_run_host_agg16.py','reservation_agg16.py']:
 p=S/name;q=B/name
 if not q.exists():shutil.copyfile(p,q)
 else:assert q.read_bytes()==p.read_bytes()
for r in plan:
 if r['source']:
  p=Path(r['source']);raw=p.read_bytes();assert hashlib.sha256(raw).hexdigest()==r['source_sha256'],r['original']
  q=B/'historical_sources'/(r['original'].replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
(B/'NDO_SEED_PINS.json').write_text(json.dumps(dict(objects=rows,source_roots=[str(P),str(S)],retarget_count=len(plan)),indent=2)+'\n')
print('copied immutable selection',len(rows),'objects; retained task cache')
