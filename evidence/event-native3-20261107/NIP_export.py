from pathlib import Path
import json,hashlib,shutil
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIP_20261107');out=C/'NIP_exports_20261107';out.mkdir(exist_ok=True)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
seed=json.loads((B/'NIP_SEED.json').read_text())
for row in seed['files']:assert sha(Path(row['source']))==row['sha256']==sha(Path(row['destination']))
rows=[]
for name in ['NIP_OuterTrace','NIP_AdmittedSupport','NIP_NestedEvents','NIP_CanonicalInput','NIP_LiteralFlag','NIP_PhysicalObserver','NIP_COMBINED_IMPORT']:
 p=B/'NIP_objects'/(name+'.olean');assert p.exists()
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.exists():
   q=out/z.name
   if q.exists():assert sha(q)==sha(z)
   else:shutil.copy2(z,q)
   rows.append(dict(source=str(z),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
result=dict(seed_verified=seed['seed_count'],objects=rows,bytes=sum(x['bytes'] for x in rows),physical_credit=False)
(B/'NIP_EXPORT.json').write_text(json.dumps(result,indent=1)+'\n');print(json.dumps(result))
