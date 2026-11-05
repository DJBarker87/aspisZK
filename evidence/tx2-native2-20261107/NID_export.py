"""Retain only own compiled exports; hash the actually selected combined closure."""
from pathlib import Path
import os,json,hashlib,shutil,lzma
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NID_exports_20261107');C.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[]
for p in sorted((B/'NID_objects').rglob('*')):
 if not p.is_file():continue
 q=C/p.relative_to(B/'NID_objects');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 assert sha(q)==sha(p)
 records.append(dict(source=str(p),destination=str(q),sha256=sha(q),bytes=q.stat().st_size))
roots=[B/'.lake/build/lib/lean',Path(os.environ['LEAN_SYSROOT'])/'lib/lean']+[Path(x) for x in os.environ['LEAN_PATH'].split(':')]
modules=[json.loads(l)['module'] for l in (B/'NID_LOADED_scan.jsonl').read_text().splitlines()]
selected=[]
for n in modules:
 rel=Path(*n.split('.')).with_suffix('.olean')
 p=next((r/rel for r in roots if (r/rel).is_file()),None)
 assert p is not None,n
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():selected.append(dict(module=n,path=str(z),sha256=sha(z),bytes=z.stat().st_size))
raw=json.dumps(dict(modules=len(modules),files=selected),separators=(',',':')).encode()
(B/'NID_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NID_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NID_EXPORT.json').write_text(json.dumps(dict(own_exports=records,export_bytes=sum(x['bytes'] for x in records),closure_modules=len(modules),closure_files=len(selected),closure_raw_bytes=len(raw),closure_sha256=hashlib.sha256(raw).hexdigest(),disk_free=shutil.disk_usage(B).free),indent=1)+'\n')
print(json.dumps(dict(exports=len(records),closure_modules=len(modules),closure_files=len(selected),raw_bytes=len(raw))))
