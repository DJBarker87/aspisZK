"""Read-only closure pinning plus tiny owned export; never modifies shared caches."""
from pathlib import Path
import json,hashlib,lzma,shutil,os,subprocess
B=Path.cwd();C=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIN_20261107')
config=json.loads((B/'NIN_L056.json').read_text());roots=config['env']['LEAN_PATH'].split(':')
loaded=[json.loads(l)['module']for l in (B/'NIN_LOADED_scan.jsonl').read_text().splitlines()]
rows=[]
for n in loaded:
 rel=n.replace('.','/')+'.olean'
 p=next((Path(r)/rel for r in roots if (Path(r)/rel).is_file()),None)
 assert p is not None,n
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():rows.append(dict(module=n,path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
assert any(x['module']=='Aeneas'for x in rows)
raw=json.dumps(dict(LEAN_PATH=roots,selected_objects=rows,modules=loaded,provenance='All actually loaded modules from NFX serialized-table scanner'),sort_keys=True).encode()
(B/'NIN_CLOSURE_PINS.json.xz').write_bytes(lzma.compress(raw,preset=6));(B/'NIN_CLOSURE_PINS.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
def suffix(path):
 for s in ['.olean.private','.olean.server','.olean','.ir']:
  if path.endswith(s):return s
 raise ValueError(path)
prior=json.loads(lzma.decompress((B/'NIN_READONLY_NIM_CLOSURE.json.xz').read_bytes()))['selected_objects']
old={(x['module'],suffix(x['path'])):x for x in prior}
variants=[];same=[];new=[]
for x in rows:
 k=(x['module'],suffix(x['path']))
 if k not in old:new.append(x)
 elif x['sha256']!=old[k]['sha256']:variants.append(dict(module=x['module'],suffix=k[1],old=old[k],new=x))
 else:same.append(k)
(B/'NIN_PREDECESSOR_COMPARISON.json').write_text(json.dumps(dict(predecessor='NIM full combined closure',same_files=len(same),variants=variants,added_files=len(new),note='Serialized variants are disclosed, not silently equated. Actual selected closure independently audited.'),indent=1)+'\n')
exports=[];out=C/'NIN_exports_20261107';out.mkdir(exist_ok=True)
for p in (B/'NIN_objects').rglob('*.olean'):
 if not p.name.startswith('NIN_')or p.stem in ['NIN_Inspect','NIN_Driver','NIN_ProofDriver']:continue
 for q in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if q.is_file():
   dest=out/q.relative_to(B/'NIN_objects');dest.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(q,dest)
   sha=hashlib.sha256(q.read_bytes()).hexdigest();assert hashlib.sha256(dest.read_bytes()).hexdigest()==sha
   exports.append(dict(source=str(q),path=str(dest),sha256=sha,bytes=q.stat().st_size))
(B/'NIN_EXPORT.json').write_text(json.dumps(dict(export=str(out),files=exports,logical_bytes=sum(x['bytes']for x in exports),cache_retained=str(C),closure_objects=len(rows),closure_bytes=sum(x['bytes']for x in rows),aeneas_files=sum(x['module']=='Aeneas'or x['module'].startswith('Aeneas.')or x['module'].startswith('AeneasMeta')for x in rows)),indent=1)+'\n')
(B/'NIN_RESTORE_PATHS.json').write_text(json.dumps([str(out)]+[r for r in roots if r!=str(B/'NIN_objects')],indent=1)+'\n')
print(json.dumps(dict(closure_files=len(rows),variants=len(variants),export_files=len(exports),export_bytes=sum(x['bytes']for x in exports))))
