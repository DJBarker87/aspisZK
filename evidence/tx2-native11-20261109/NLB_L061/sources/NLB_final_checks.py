"""Own retained-object export and actual loaded-closure pinning; read-only inputs."""
from pathlib import Path
import json,hashlib,shutil,lzma,subprocess
B=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
modules=json.loads((B/'NLB_MODULES.json').read_text())+['NLB_COMBINED_IMPORT']
pins=json.loads((B/'NLB_SOURCE_PINS.json').read_text())
errors=[m for m,h in pins.items() if sha(B/'NLB_generated'/(m+'.lean'))!=h]
assert not errors,errors
records=[];out=B/'NLB_exports_20261109';out.mkdir(exist_ok=True)
for m in modules:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NLB_objects'/(m+suffix)
  if not p.exists():continue
  q=out/p.name
  if q.exists():assert sha(q)==sha(p),(q,'different retained export')
  else:shutil.copyfile(p,q)
  records.append(dict(source=str(p),path=str(q),sha256=sha(p),bytes=p.stat().st_size))
(B/'NLB_EXPORT.json').write_text(json.dumps(dict(path=str(out),files=records,bytes=sum(z['bytes'] for z in records)),indent=2)+'\n')
rows=[json.loads(s) for s in (B/'NLB_LOADED_scan.jsonl').read_text().splitlines() if s.strip()]
assert rows and all(not r['dangling'] and not r['duplicate_owners'] and r['imports_match'] for r in rows)
paths=json.loads((B/'NLB_PATHS.json').read_text());closure={}
for row in rows:
 m=row['module'];rel=m.replace('.','/')
 p=next((Path(root)/(rel+'.olean') for root in paths if (Path(root)/(rel+'.olean')).is_file()),None);assert p is not None,m
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():closure[str(q)]=dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size)
raw=json.dumps(closure,sort_keys=True).encode();(B/'NLB_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NLB_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
(B/'NLB_SOURCE_VERIFICATION.json').write_text(json.dumps(dict(source_modules=len(pins),source_errors=errors,rust_not_run=True,closure_modules=len(rows),closure_objects=len(closure),export_objects=len(records),free_bytes=shutil.disk_usage(B).free),indent=2)+'\n')
W=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025');T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
tools=[B/'S2W_run_host.py',B/'NLB_native/NFA_WALKER.c',B/'NLB_native/NFA_MemoryLimit.c']+[W/n for n in ['S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']]+[T/'bin'/n for n in ['lean','lake','leanc']]
(B/'NLB_TOOL_PINS.json').write_text(json.dumps({str(q):sha(q) for q in tools},indent=2)+'\n')
(B/'NLB_target').mkdir(exist_ok=True)
own_bytes=int(subprocess.check_output(['du','-sb',str(B)],text=True).split()[0]);assert own_bytes<30_000_000_000,own_bytes
(B/'NLB_RETENTION.json').write_text(json.dumps(dict(workspace=str(B),own_workspace_bytes=own_bytes,free_bytes=shutil.disk_usage(B).free,cache=str(out),cargo_target=str(B/'NLB_target'),retained_objects=modules,cache_deleted=False,keys_touched=False),indent=2)+'\n')
(B/'NLB_CLEANUP.json').write_text(json.dumps(dict(deleted=[],cache_deleted=False,keys_touched=False,retained_target=True,reason='Retain own workspace/export/TMPDIR/target. No destructive cleanup.'))+'\n')
print(json.dumps(dict(source_modules=len(pins),closure_modules=len(rows),export_bytes=sum(z['bytes'] for z in records),own_bytes=own_bytes,free_bytes=shutil.disk_usage(B).free)))
