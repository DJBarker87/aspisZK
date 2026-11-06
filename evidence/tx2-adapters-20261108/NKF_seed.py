from NKF_transport import *
admission('NKF_P001')
r=ssh('python3','''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});out=[]
for src,name in [('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKC_20261108/NKC_exports_20261108','NKF_NKC_seed'),('/home/dombarker/project-offloads/codex-cx-tx2-decoders3-20261107/NJY_exports_final_20261108','NKF_NJY_seed')]:
 root=Path(src);dest=b/name;assert root.is_dir();dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q);pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=src,destination=str(dest),bytes=sum(x['bytes'] for x in pins),pins=pins))
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-decoders3-20261107')
for n in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/n,b/n)
(b/'NKF_objects').mkdir(exist_ok=True)
print(json.dumps(dict(seeds=out,free_bytes=shutil.disk_usage(b).free)))
'''.format(B=B));assert r.returncode==0,r.stderr
(E/'NKF_SEED.json').write_text(r.stdout)
env=json.loads((E.parent/'tx2-decoders3-20261108/NJY_ENV.json').read_text())
paths=json.loads((E.parent/'ledger17-20261108/NKC_PATHS.json').read_text())
if isinstance(paths,dict):print('PATH_KEYS',list(paths));paths=paths.get('paths',paths.get('LEAN_PATH'))
if isinstance(paths,str):paths=paths.split(':')
env['LEAN_PATH']=':'.join([B+'/NKF_objects',B+'/NKF_NKC_seed',B+'/NKF_NJY_seed']+paths+env['LEAN_PATH'].split(':'))
(E/'NKF_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
print(json.dumps({x['destination']:x['bytes'] for x in json.loads(r.stdout)['seeds']}))
