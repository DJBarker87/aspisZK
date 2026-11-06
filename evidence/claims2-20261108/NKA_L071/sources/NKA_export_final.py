from pathlib import Path
import json,hashlib,shutil,lzma
B=Path(__file__).resolve().parent;T=Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0')
D=Path('/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NKA_exports_final_20261108')
assert not D.exists();D.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
paths=json.loads((B/'NKA_PATHS.json').read_text());roots=[Path(x) for x in paths]+[T/'lib/lean']
modules=json.loads((B/'NKA_MODULES.json').read_text());names=[m['module'] for m in modules]+['NKA_COMBINED_IMPORT'];files=[]
for name in names:
 q=next((root/(name.replace('.','/')+'.olean') for root in roots if (root/(name.replace('.','/')+'.olean')).is_file()),None);assert q is not None,name
 for p in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
  if p.is_file():
   dest=D/p.name;shutil.copyfile(p,dest);assert sha(dest)==sha(p)
   files.append(dict(module=name,source=str(p),path=str(dest),bytes=p.stat().st_size,sha256=sha(p)))
resolved=[]
for line in (B/'NKA_LOADED_scan.jsonl').read_text().splitlines():
 name=json.loads(line)['module'];rel=name.replace('.','/')+'.olean'
 q=next((root/rel for root in roots if (root/rel).is_file()),None);assert q is not None,name
 for p in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
  if p.is_file():resolved.append(dict(module=name,path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
raw=json.dumps(dict(selected=resolved,cargo_target_dir=str(B/'NKA_target')),sort_keys=True).encode()
(B/'NKA_RESOLVED_OBJECTS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NKA_RESOLVED_OBJECTS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
consumer=[str(D),*[p for p in paths if p!=str(B/'NKA_objects')]]
(B/'NKA_CONSUMER_PATHS.json').write_text(json.dumps(consumer,indent=2)+'\n')
(B/'NKA_EXPORT.json').write_text(json.dumps(dict(directory=str(D),files=files,total_bytes=sum(p['bytes'] for p in files),modules=len(names),resolved_files=len(resolved),cargo_target_dir=str(B/'NKA_target')),indent=2)+'\n')
archives=B/'NKA_archives_final';archives.mkdir(exist_ok=True)
for p in B.glob('NEP_fixtures_*'):
 if p.is_file():
  raw=p.read_bytes();(archives/(p.name+'.xz')).write_bytes(lzma.compress(raw,preset=6));(archives/(p.name+'.sha256')).write_text(hashlib.sha256(raw).hexdigest()+'\n');p.unlink()
print('NJT retained export and complete selected-object pins written')

# Retain exact tool inputs and fixture object selections; these are immutable
# predecessors and the SAME compiled driver used for fixtures and both groups.
tools=[]
for p in [T/'bin/lean',T/'bin/lake',T/'bin/leanc',Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),Path('/home/dombarker/.kani/kani-0.67.0/library/kani/kani_lib.c'),B/'lean-toolchain',B/'lakefile.toml',B/'lake-manifest.json']:
 if p.is_file():tools.append(dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)))
fixtures=[]
for name in ['NEP_Planted','NEP_Mutations','NFA_WALKER','NFA_MemoryLimit']:
 q=next((root/(name+'.olean') for root in roots if (root/(name+'.olean')).is_file()),None);assert q is not None,name
 for p in [q,Path(str(q)+'.private'),Path(str(q)+'.server'),q.with_suffix('.ir')]:
  if p.is_file():fixtures.append(dict(module=name,path=str(p),sha256=sha(p),bytes=p.stat().st_size))
(B/'NKA_TOOL_PINS.json').write_text(json.dumps(dict(tools=tools,fixtures=fixtures,library_pins='NKA_LIBRARY_PINS.json',drivers=json.loads((B/'NKA_LINK.json').read_text())),indent=2))
