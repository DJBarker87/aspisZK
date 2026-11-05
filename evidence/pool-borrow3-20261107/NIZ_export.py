"""Retain prefix-owned objects and pin the actually resolved scanned closure."""
from pathlib import Path
import os,json,hashlib,lzma,shutil
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
rows=[]
for base,dest in [(B/'NIZ_objects',C/'NIZ_exports_20261107'),(B/'NIZ_native',C/'NIZ_audit_native_20261107')]:
 dest.mkdir(exist_ok=True)
 for p in base.rglob('*'):
  if not p.is_file():continue
  q=dest/p.relative_to(base);q.parent.mkdir(exist_ok=True,parents=True)
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),path=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NIZ_EXPORT.json').write_text(json.dumps(dict(exports=rows,export_bytes=sum(r['bytes'] for r in rows),cache_retained=str(C)),indent=1)+'\n')
roots=os.environ['LEAN_PATH'].split(':');scan=B/'NIZ_LOADED_scan.jsonl'
modules=[json.loads(l)['module'] for l in scan.read_text().splitlines()]
pins=[]
for name in modules:
 rel=name.replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None)
 assert p is not None,name
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():pins.append(dict(module=name,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(lean_path=roots,scan_sha256=sha(scan),modules=len(modules),files=pins),separators=(',',':')).encode()
(B/'NIZ_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6))
(B/'NIZ_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('NIO export retained; resolved closure '+str(len(modules))+' modules / '+str(len(pins))+' files')
