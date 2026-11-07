from pathlib import Path
import os,json,hashlib,shutil
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();rows=[]
for name,dest in [('NMX_NND_OBJECT_INPUTS.json','NMX_NND_seed'),('NMX_LIB_A_OBJECT_INPUTS.json','NMX_LIB_seed')]:
 x=json.loads((B/name).read_text());files=x['files'];items=[dict(path=k,**v) for k,v in files.items()] if isinstance(files,dict) else files
 for row in items:
  p=Path(row['path']);assert sha(p)==row['sha256'],('published input drift',p)
  q=B/dest/p.name;q.parent.mkdir(exist_ok=True)
  if q.exists():assert sha(q)==sha(p),('own seed drift',q)
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),copy=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NMX_REGISTRY_SEED.json').write_text(json.dumps(rows,indent=1)+'\n');print(json.dumps(dict(status='PASS',files=len(rows),deletions=0)))
