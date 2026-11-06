from pathlib import Path
import json,hashlib,shutil,lzma
B=Path(__file__).resolve().parent;T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJT_exports_20261108')
assert not D.exists();D.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=json.loads((B/'NJT_PATHS.json').read_text());roots=[Path(x) for x in paths]+[T/'lib/lean']
modules=json.loads((B/'NJT_MODULES.json').read_text());names=[m['module'] for m in modules]+['NJT_COMBINED_IMPORT'];files=[]
for name in names:
 q=next((root/(name.replace('.','/')+'.olean') for root in roots if (root/(name.replace('.','/')+'.olean')).is_file()),None);assert q is not None,name
 for p in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
  if p.is_file():
   dest=D/p.name;shutil.copyfile(p,dest);assert sha(dest)==sha(p)
   files.append(dict(module=name,source=str(p),path=str(dest),bytes=p.stat().st_size,sha256=sha(p)))
resolved=[]
for line in (B/'NJT_LOADED_scan.jsonl').read_text().splitlines():
 name=json.loads(line)['module'];rel=name.replace('.','/')+'.olean'
 q=next((root/rel for root in roots if (root/rel).is_file()),None);assert q is not None,name
 for p in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
  if p.is_file():resolved.append(dict(module=name,path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
raw=json.dumps(dict(selected=resolved,cargo_target_dir=str(B/'NJT_target')),sort_keys=True).encode()
(B/'NJT_RESOLVED_OBJECTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NJT_RESOLVED_OBJECTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
consumer=[str(D),*[p for p in paths if p!=str(B/'NJT_objects')]]
(B/'NJT_CONSUMER_PATHS.json').write_text(json.dumps(consumer,indent=2)+'\n')
(B/'NJT_EXPORT.json').write_text(json.dumps(dict(directory=str(D),files=files,total_bytes=sum(p['bytes'] for p in files),modules=len(names),resolved_files=len(resolved),cargo_target_dir=str(B/'NJT_target')),indent=2)+'\n')
archives=B/'NJT_archives';archives.mkdir(exist_ok=True)
for p in B.glob('NEP_fixtures_*'):
 if p.is_file():
  raw=p.read_bytes();(archives/(p.name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(archives/(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
print('NJT retained export and complete selected-object pins written')
