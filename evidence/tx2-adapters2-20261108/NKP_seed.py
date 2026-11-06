from NKP_transport import *
import hashlib
admission('NKP_P001')
r=ssh('python3',"""from pathlib import Path
import shutil,json,hashlib
b=Path(BB);out=[]
for src,name in [('/home/dombarker/project-offloads/codex-cx-tx2-adapters-20261107/NKF_exports_resume_20261108','NKP_NKF_seed'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKH_20261108/NKH_exports_20261108','NKP_NKH_seed')]:
 root=Path(src);dest=b/name;assert root.is_dir();dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q);pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=src,destination=str(dest),bytes=sum(x['bytes'] for x in pins),pins=pins))
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters-20261107')
for n in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/n,b/n)
for n in ['NKP_objects','NKP_tmp','NKP_target']:(b/n).mkdir(exist_ok=True)
(b/'NKP_tmp/.keep').touch()
# One private scratch tree; retain every source input, exclude build outputs and solver temporaries.
shutil.copytree(src/'NKF_src',b/'NKP_src',ignore=shutil.ignore_patterns('target','__pycache__','rustc-ice*'))
print(json.dumps(dict(seeds=out,rust_seed_bytes=sum(p.stat().st_size for p in (b/'NKP_src').rglob('*') if p.is_file()),free_bytes=shutil.disk_usage(b).free)))
""".replace('BB',repr(B)));assert r.returncode==0,r.stderr
(E/'NKP_SEED.json').write_text(r.stdout)
env=json.loads((E.parent/'tx2-adapters-20261108/NKF_ENV.json').read_text())
paths=json.loads((E.parent/'ledger18-20261108/NKH_PATHS.json').read_text())
assert isinstance(paths,list)
env['LEAN_PATH']=':'.join([B+'/NKP_objects',B+'/NKP_NKF_seed',B+'/NKP_NKH_seed']+paths+env['LEAN_PATH'].split(':'))
env['TMPDIR']=B+'/NKP_tmp';env['CARGO_TARGET_DIR']=B+'/NKP_target'
(E/'NKP_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
print(json.dumps({x['destination']:x['bytes'] for x in json.loads(r.stdout)['seeds']}))
