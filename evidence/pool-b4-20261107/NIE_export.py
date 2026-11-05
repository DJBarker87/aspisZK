"""Non-destructive owned-cache export and exact audited closure pins; no compiler."""
from pathlib import Path
import json,hashlib,shutil,lzma,os
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104')
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
exports=[]
for source,target in [(B/'NIE_objects',C/'NIE_exports_20261107'),(B/'NIE_native',C/'NIE_audit_native_20261107')]:
 target.mkdir(exist_ok=True)
 for p in sorted(source.rglob('*')):
  if not p.is_file():continue
  rel=p.relative_to(source)
  if source.name=='NIE_objects' and not p.name.startswith('NIE_'):continue
  q=target/rel;q.parent.mkdir(parents=True,exist_ok=True);h=sha(p);copied=False
  if q.exists():assert sha(q)==h,('Retain existing cache; conflicting export',str(q))
  else:shutil.copy2(p,q);copied=True
  assert sha(q)==h
  exports.append(dict(source=str(p),path=str(q),sha256=h,bytes=p.stat().st_size,copied=copied))
config=json.loads((B/'NIE_L014.json').read_text());roots=config['env']['LEAN_PATH'].split(':');scan=[json.loads(s) for s in (B/'NIE_LOADED_scan.jsonl').read_text().splitlines()]
manifest=[];missing=[];exported={r['source']:r for r in exports}
for row in scan:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if (Path(root)/rel).is_file()),None)
 if p is None:missing.append(row['module']);continue
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.is_file():continue
  h=sha(z);retained=exported.get(str(z));manifest.append(dict(module=row['module'],resolved_path=str(z),retained_path=retained['path'] if retained else str(z),sha256=h,bytes=z.stat().st_size))
assert not missing,missing
raw=json.dumps(dict(roots=roots,modules=len(scan),objects=manifest,missing=missing,source='NIE_L014 actual loaded module closure; own copied exports have identical bytes'),sort_keys=True).encode()
(B/'NIE_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NIE_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
free=shutil.disk_usage(B)
result=dict(cache_retained=str(C),exports=exports,own_export_bytes=sum(r['bytes'] for r in exports),closure_modules=len(scan),closure_objects=len(manifest),closure_object_bytes=sum(r['bytes'] for r in manifest),closure_uncompressed_sha256=hashlib.sha256(raw).hexdigest(),source_revision=config['source_revision'],disk=dict(total=free.total,used=free.used,free=free.free),no_cache_deletion=True)
(B/'NIE_EXPORT.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(export_files=len(exports),export_bytes=result['own_export_bytes'],closure_modules=len(scan),closure_objects=len(manifest),disk_free_bytes=free.free)))
