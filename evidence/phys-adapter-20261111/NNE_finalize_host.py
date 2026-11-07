from pathlib import Path
import hashlib,json,shutil
b=Path.cwd()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
exports=b/'NNE_exports_20261111';exports.mkdir(exist_ok=True)
mods=json.loads((b/'NNE_EXPORT_MODULES.json').read_text())
rows=[]
for m in mods:
 for p in (b/'NNE_objects').glob(m+'.*'):
  q=exports/p.name
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(module=m,path=str(q),sha256=sha(q),bytes=q.stat().st_size))
assert {x['module'] for x in rows}==set(mods)
aeneas={}
for p in b.glob('NNE_L*/receipt.json'):
 r=json.loads(p.read_text())
 for n,x in r.get('deps_fingerprint',{}).get('selected_objects',{}).items():
  if '/Aeneas/' in n or '/AeneasMeta/' in n or Path(n).name in ['Aeneas.olean','AeneasMeta.olean']:
   if n in aeneas:assert aeneas[n]==x['sha256']
   aeneas[n]=x['sha256']
for n,h in aeneas.items():assert sha(Path(n))==h,n
(b/'NNE_EXPORT.json').write_text(json.dumps(dict(directory=str(exports),objects=rows),indent=1)+'\n')
(b/'NNE_RETENTION.json').write_text(json.dumps(dict(workspace=str(b),workspace_bytes=sum(p.stat().st_size for p in b.rglob('*') if p.is_file()),host_free_bytes=shutil.disk_usage(b).free,aeneas_files_verified=len(aeneas),export_files=len(rows),deletions=0,cache_and_tmp_retained=True),indent=1)+'\n')
print(json.dumps(dict(exports=len(rows),aeneas_verified=len(aeneas),free=shutil.disk_usage(b).free)))
