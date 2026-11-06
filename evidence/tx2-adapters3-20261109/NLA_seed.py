from NLA_transport import *
import hashlib
admission('NLA_P001')
r=ssh('python3',"""from pathlib import Path
import shutil,json,hashlib
b=Path(BB);out=[]
for src,name in [('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_exports_final_20261108','NLA_NKP_seed'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKW_20261109/NKW_exports_20261109','NLA_NKW_seed')]:
 root=Path(src);dest=b/name;assert root.is_dir();dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q);pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=src,destination=str(dest),bytes=sum(x['bytes'] for x in pins),pins=pins))
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108')
for n in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/n,b/n)
for n in ['NLA_objects','NLA_tmp','NLA_target']:(b/n).mkdir(exist_ok=True)
(b/'NLA_tmp/.keep').touch()
shutil.copytree(src/'NKP_src',b/'NLA_src',ignore=shutil.ignore_patterns('target','__pycache__','rustc-ice*'))
print(json.dumps(dict(seeds=out,rust_seed_bytes=sum(p.stat().st_size for p in (b/'NLA_src').rglob('*') if p.is_file()),free_bytes=shutil.disk_usage(b).free)))
""".replace('BB',repr(B)));assert r.returncode==0,r.stderr
(E/'NLA_SEED.json').write_text(r.stdout)
env=json.loads((E.parent/'tx2-adapters2-20261108/NKP_ENV.json').read_text())
paths=json.loads((E.parent/'ledger20-20261109/NKW_PATHS.json').read_text())
env['LEAN_PATH']=':'.join([B+'/NLA_objects',B+'/NLA_NKP_seed',B+'/NLA_NKW_seed']+paths+env['LEAN_PATH'].split(':'))
env['TMPDIR']=B+'/NLA_tmp';env['CARGO_TARGET_DIR']=B+'/NLA_target'
(E/'NLA_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
print(json.dumps({x['destination']:x['bytes'] for x in json.loads(r.stdout)['seeds']}))
