"""Retain own validated objects and pin the actual NFX-loaded dependency closure."""
from pathlib import Path
import json,hashlib,shutil,lzma,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((B/'NLW_MODULES.json').read_text())+['NLW_COMBINED_IMPORT']
manifest={m:sha(B/'NLW_generated'/(m+'.lean')) for m in modules}
h=hashlib.sha256(json.dumps(manifest,sort_keys=True).encode()).hexdigest()
out=B/('NLW_exports_20261110_'+h[:12]);out.mkdir(exist_ok=True);records=[]
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NLW_objects'/(m+suffix)
  if not p.exists():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p),('retained export collision',q)
  else:shutil.copyfile(p,q)
  records.append(dict(module=m,source=str(p),path=str(q),sha256=sha(p),bytes=p.stat().st_size))
(B/'NLW_EXPORT.json').write_text(json.dumps(dict(path=str(out),source_manifest_sha256=h,source_hashes=manifest,files=records,bytes=sum(r['bytes'] for r in records)),indent=1)+'\n')
rows=[json.loads(l) for l in (B/'NLW_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows)
roots=os.environ['LEAN_PATH'].split(':');pins={}
for row in rows:
 rel=row['module'].replace('.','/')+'.olean'
 p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p is not None,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins[str(q)]=dict(module=row['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size)
raw=json.dumps(pins,sort_keys=True).encode();(B/'NLW_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw))
(B/'NLW_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps(dict(export_objects=len(records),closure_objects=len(pins),bytes=sum(r['bytes'] for r in records))))
