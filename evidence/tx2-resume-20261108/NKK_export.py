"""Copy own validated objects; pin the actual NFX-loaded closure."""
from pathlib import Path
import json,hashlib,shutil,lzma
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((B/'NKK_MODULES.json').read_text())+['NKK_COMBINED_IMPORT']
out=B/'NKK_exports_final_20261108';out.mkdir(exist_ok=True);records=[]
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NKK_objects'/(m+suffix)
  if not p.exists():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p),(q,'retained export collision')
  else:shutil.copyfile(p,q)
  records.append(dict(source=str(p),path=str(q),sha256=sha(p),bytes=p.stat().st_size))
(B/'NKK_EXPORT.json').write_text(json.dumps(dict(path=str(out),files=records,bytes=sum(z['bytes'] for z in records)),indent=2)+'\n')
rows=[json.loads(s) for s in (B/'NKK_LOADED_scan.jsonl').read_text().splitlines() if s.strip()]
paths=json.loads((B/'NKK_PATHS.json').read_text());closure={}
for row in rows:
 m=row['module'];rel=m.replace('.','/')
 p=next((Path(root)/(rel+'.olean') for root in paths if (Path(root)/(rel+'.olean')).is_file()),None);assert p is not None,m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure[str(q)]=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size)
raw=json.dumps(closure,sort_keys=True).encode()
(B/'NKK_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6))
(B/'NKK_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(export_objects=len(records),closure_objects=len(closure),bytes=sum(z['bytes'] for z in records))))

exec(compile((B/"NKK_retention.py").read_text(),str(B/"NKK_retention.py"),"exec"))
