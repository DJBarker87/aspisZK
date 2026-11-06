from pathlib import Path
import json,hashlib,shutil
B=Path.cwd().resolve();assert B.name=='codex-cx-entry-leaves-20261107'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NJH_EXPORT.json').read_text());cache=Path(x['path'])
for r in x['files']:assert sha(cache/r['path'])==r['sha256']
lock=json.loads((B/'NJH_K013-lock-check.json').read_text());assert lock['unchanged'] and sha(B/'NJH_src/Cargo.lock')==lock['after']
rows=[]
for name in ['NJH_target','NJH_native']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():
  pins=[dict(path=str(z),sha256=sha(z),bytes=z.stat().st_size) for z in p.rglob('*') if z.is_file()] if name=='NJH_native' else []
  rows.append(dict(path=str(p),bytes=sum(z.stat().st_size for z in p.rglob('*') if z.is_file()),binary_pins=pins));shutil.rmtree(p)
removed=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (B/'NJH_tmp').rglob(pattern):
  if p.is_file():removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
x=dict(removed=rows,solver_scratch=removed,retained_cache=str(cache),retained_seed=str(B/'NJH_seed'),retained_objects=str(B/'NJH_objects'),source_lock_unchanged=True,free_bytes=shutil.disk_usage(B).free)
(B/'NJH_HOST_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k not in ['removed','solver_scratch']}))
