"""Own pin/export validation. Does not modify shared sources or infrastructure."""
from pathlib import Path
import json,hashlib,shutil,lzma
B=Path(__file__).resolve().parent;C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((B/'NKO_MODULES.json').read_text())+['NKO_COMBINED_IMPORT'];pins=json.loads((B/'NKO_SOURCE_PINS.json').read_text())
suffix='\n#[cfg(kani)]\n#[path = "NKO_parent.rs"]\nmod NKO_parent;\n'
def source_hash(n):
 p=B/'NKO_src'/n
 if n.endswith('/candidate.rs'):
  t=p.read_text();assert t.endswith(suffix);return hashlib.sha256(t[:-len(suffix)].encode()).hexdigest()
 if n=='crates/aspis-r1-cost-probe/src/lib.rs':
  return hashlib.sha256(p.read_text().replace('#![cfg_attr(kani,feature(allocator_api))]\n','').encode()).hexdigest()
 return sha(p)
errors=[n for n,h in pins.items() if source_hash(n)!=h];assert not errors,errors
assert sha(B/'NKO_src/Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
records=[];out=B/'NKO_exports_20261108';out.mkdir(exist_ok=True)
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NKO_objects'/(m+suffix)
  if not p.exists():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p),(q,'do not overwrite different retained export')
  else:shutil.copyfile(p,q)
  records.append(dict(source=str(p),path=str(q),sha256=sha(p),bytes=p.stat().st_size))
(B/'NKO_EXPORT.json').write_text(json.dumps(dict(path=str(out),files=records,bytes=sum(z['bytes'] for z in records)),indent=2)+'\n')
# Resolve the actual closure that passed NFX, then pin all object companions.
rows=[json.loads(s) for s in (B/'NKO_LOADED_scan.jsonl').read_text().splitlines() if s.strip()]
paths=json.loads((B/'NKO_PATHS.json').read_text());closure={}
for row in rows:
 m=row['module'];rel=m.replace('.','/')
 p=next((Path(root)/(rel+'.olean') for root in paths if (Path(root)/(rel+'.olean')).is_file()),None);assert p is not None,m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure[str(q)]=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size)
raw=json.dumps(closure,sort_keys=True).encode();(B/'NKO_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NKO_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NKO_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(source_files=len(pins),source_errors=errors,lock_unchanged=True,closure_modules=len(rows),closure_objects=len(closure),export_objects=len(records),free_bytes=shutil.disk_usage(B).free),indent=2)+'\n')
W=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
tool_paths=[B/'S2W_run_host.py',B/'NKO_native/NFA_WALKER.c',B/'NKO_native/NFA_MemoryLimit.c']+[W/n for n in ['S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']]+[T/'bin'/n for n in ['lean','lake','leanc']]
(B/'NKO_TOOL_PINS.json').write_text(json.dumps({str(q):sha(q) for q in tool_paths},indent=2)+'\n')
(B/'NKO_RETENTION.json').write_text(json.dumps(dict(workspace=str(B),cache=str(out),cargo_target=str(B/'NKO_target'),retained_objects=modules,cache_deleted=False,keys_touched=False),indent=2)+'\n')
print(json.dumps(dict(source_files=len(pins),closure_modules=len(rows),export_bytes=sum(z['bytes'] for z in records),free_bytes=shutil.disk_usage(B).free)))

(B/'NKO_CLEANUP.json').write_text(json.dumps(dict(deleted=[],keys_touched=False,retained_target=True,reason='Retain own workspace, cache, TMPDIR and target; no destructive cleanup.'))+'\n')
