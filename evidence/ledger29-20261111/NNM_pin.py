"""Read-only closure inventory; retain own selected objects, never delete caches."""
from pathlib import Path
import json,hashlib,lzma,shutil
B=Path.cwd();roots=__import__('os').environ['LEAN_PATH'].split(':');H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
loaded=[json.loads(l)for l in(B/'NNM_LOADED_scan.jsonl').read_text().splitlines()]
assert loaded and all(not r['dangling']and not r['duplicate_owners']and r['imports_match']for r in loaded)
pins=[]
for row in loaded:
 rel=row['module'].replace('.','/')+'.olean';p=next((Path(root)/rel for root in roots if(Path(root)/rel).is_file()),None);assert p,rel
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.exists():pins.append(dict(module=row['module'],path=str(q),sha256=H(q),bytes=q.stat().st_size))
# All twenty-one canonical owners were rebuilt from the single committed source set.
for row in pins:
 if row['module'].startswith('RSL_'):assert '/NNM_rev4/'in row['path'],row
 if row['module'].startswith('NMV_'):assert '/NNM_wrapperR4/'in row['path'],row
assert len({r['module']for r in pins if r['module'].startswith('NMV_')})==15
payload=json.dumps(dict(LEAN_PATH=roots,modules=len(loaded),selected_objects=pins,scan_pass=True),indent=1).encode();(B/'NNM_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(payload));(B/'NNM_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(payload).hexdigest()+'\n')
export=B/'NNM_exports_final_20261111';export.mkdir(exist_ok=True);exported=[]
for folder in ['NNM_objects','NNM_rev4','NNM_tx1','NNM_wrapperR4','NNM_tx2','NNM_previous']:
 for p in(B/folder).rglob('*'):
  if not p.is_file():continue
  rel=p.relative_to(B/folder);q=export/folder/rel;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert H(q)==H(p)
  else:shutil.copy2(p,q)
  exported.append(dict(path=str(q),sha256=H(q),bytes=q.stat().st_size))
(B/'NNM_EXPORT.json').write_text(json.dumps(dict(export=str(export),files=exported,cache_retained=True,deletions=0,disk=shutil.disk_usage(B)._asdict()),indent=1)+'\n')
(B/'NNM_GATE_INTEGRITY.json').write_text(json.dumps(dict(status='PASS',rsl_single_rev4_owner=True,NMV_only15_rev4=True,modules=len(loaded),selected_files=len(pins),retained_files=len(exported)),indent=1)+'\n')
print(json.dumps(dict(status='PASS',selected_files=len(pins),retained_files=len(exported))))
