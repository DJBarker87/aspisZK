"""Pin the full actually selected combined module closure after its NFX scan."""
from pathlib import Path
import json,os,hashlib,lzma,sys
B=Path.cwd();roots=[Path(p)for p in os.environ['LEAN_PATH'].split(':')]+[Path(os.environ['LEAN_SYSROOT'])/'lib/lean']
def sha(p):
 with p.open('rb')as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=[json.loads(l)for l in(B/'NMB_LOADED_scan.jsonl').read_text().splitlines()]
assert all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in rows)
checkpoint=B/'NMB_CLOSURE_CHECKPOINT.jsonl';files={}
meta=dict(scan_sha256=sha(B/'NMB_LOADED_scan.jsonl'),roots=[str(p)for p in roots]);mp=B/'NMB_CLOSURE_CHECKPOINT_META.json'
if mp.exists():assert json.loads(mp.read_text())==meta
else:mp.write_text(json.dumps(meta))
if checkpoint.exists():
 assert '--resume' in sys.argv,'Existing closure checkpoint: explicit recovery required'
 for line in checkpoint.read_text().splitlines():
  row=json.loads(line);p=Path(row['path']);assert p.stat().st_size==row['value']['bytes'] and p.stat().st_mtime_ns==row['mtime_ns'];files[row['path']]=row['value']
log=checkpoint.open('a')
for row in rows:
 rel=row['module'].replace('.','/')+'.olean';p=next((r/rel for r in roots if(r/rel).is_file()),None);assert p,rel
 for f in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if f.is_file() and str(f)not in files:
   files[str(f)]=dict(sha256=sha(f),bytes=f.stat().st_size)
   log.write(json.dumps(dict(path=str(f),value=files[str(f)],mtime_ns=f.stat().st_mtime_ns))+'\n');log.flush()
log.close()
raw=json.dumps(dict(module_count=len(rows),roots=[str(r)for r in roots],files=files),sort_keys=True).encode();compressed=lzma.compress(raw)
(B/'NMB_CLOSURE_PINS.json.xz').write_bytes(compressed);(B/'NMB_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
summary=dict(modules=len(rows),files=len(files),bytes=sum(r['bytes']for r in files.values()),json_sha256=hashlib.sha256(raw).hexdigest(),archive_sha256=hashlib.sha256(compressed).hexdigest(),aeneas_files=sum('/Aeneas' in n for n in files),unchanged_inputs=True)
(B/'NMB_CLOSURE_SUMMARY.json').write_text(json.dumps(summary,indent=1)+'\n');print(json.dumps(summary))
