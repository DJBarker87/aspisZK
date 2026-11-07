"""Retain own objects and hash the final imported closure; no shared writes."""
from pathlib import Path
import json,hashlib,shutil,lzma,os
B=Path.cwd();sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=['NMD_CutState','NMD_SegmentFold','NMD_CandidateFold','NMD_ComputedFold','NMD_COMBINED_IMPORT']
sources={m:sha(B/'NMD_generated'/(m+'.lean')) for m in modules};key=hashlib.sha256(json.dumps(sources,sort_keys=True).encode()).hexdigest()
out=B/('NMD_exports_'+key[:12]);out.mkdir(exist_ok=True);files=[]
for m in modules:
 for ext in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NMD_objects'/(m+ext)
  if not p.is_file():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p)
  else:shutil.copyfile(p,q)
  files.append(dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
(B/'NMD_EXPORT.json').write_text(json.dumps(dict(path=str(out),source_hashes=sources,files=files,bytes=sum(r['bytes'] for r in files)),indent=1)+'\n')
loaded=[json.loads(l) for l in (B/'NMD_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in loaded)
roots=os.environ['LEAN_PATH'].split(':');pins={}
for r in loaded:
 rel=r['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None);assert p,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():pins[str(q)]=dict(module=r['module'],path=str(q),sha256=sha(q),bytes=q.stat().st_size)
raw=json.dumps(pins,sort_keys=True).encode();(B/'NMD_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw));(B/'NMD_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
last=json.loads((B/'NMD_L013.json').read_text());aeneas={p:v for p,v in last['deps_fingerprint']['selected_objects'].items() if '/Aeneas' in p}
assert all(sha(Path(p))==v['sha256'] for p,v in aeneas.items())
retention=dict(export_objects=len(files),closure_objects=len(pins),loaded_modules=len(loaded),aeneas_objects=len(aeneas),aeneas_unchanged=True,workspace_bytes=sum(p.stat().st_size for p in B.rglob('*') if p.is_file()),free_bytes=shutil.disk_usage(B).free,removed_files=0)
assert retention['workspace_bytes']<30_000_000_000
(B/'NMD_RETENTION.json').write_text(json.dumps(retention,indent=1)+'\n');print(json.dumps(retention))
