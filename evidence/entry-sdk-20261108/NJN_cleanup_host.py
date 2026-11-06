from pathlib import Path
import json,hashlib,shutil
B=Path.cwd().resolve();assert B.name=='codex-cx-entry-sdk-20261108'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
x=json.loads((B/'NJN_EXPORT.json').read_text());cache=Path(x['path'])
for r in x['files']:assert sha(cache/r['path'])==r['sha256']
locks=[json.loads(p.read_text()) for p in B.glob('NJN_K*-lock-check.json')]
assert locks and all(x['unchanged'] and x['before']==x['after']==sha(B/'NJN_src/Cargo.lock') for x in locks)
rows=[]
for name in ['NJN_target','NJN_native']:
 p=B/name;assert p.parent==B and not p.is_symlink()
 if p.exists():
  pins=[dict(path=str(z),sha256=sha(z),bytes=z.stat().st_size) for z in p.rglob('*') if z.is_file()] if name=='NJN_native' else []
  rows.append(dict(path=str(p),bytes=sum(z.stat().st_size for z in p.rglob('*') if z.is_file()),binary_pins=pins));shutil.rmtree(p)
removed=[]
for pattern in ['external-sat*.cnf','smt2_dec_problem*']:
 for p in (B/'NJN_tmp').rglob(pattern):
  if p.is_file():removed.append(dict(path=str(p),bytes=p.stat().st_size));p.unlink()
x=dict(removed=rows,solver_scratch=removed,retained_cache=str(cache),retained_seed=str(B/'NJN_seed'),retained_objects=str(B/'NJN_objects'),source_lock_unchanged=True,free_bytes=shutil.disk_usage(B).free)
(B/'NJN_HOST_END.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps({k:v for k,v in x.items() if k not in ['removed','solver_scratch']}))
