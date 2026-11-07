from NMM_transport import *
import hashlib
admission('NMM_P001', scope=False)
sources=[('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110','NMM_NLX_seed'),('/home/dombarker/project-offloads/codex-cx-tx2-adapters4-20261110/NLK_exports_20261110_256baac6480','NMM_NLK_seed'),('/home/dombarker/project-offloads/codex-cx-cut-pilot-20261110/NMD_exports_7299666cbf38','NMM_NMD_seed')]
code="""from pathlib import Path
import shutil,json,hashlib
b=Path(BB);out=[]
for src,name in SS:
 root=Path(src);dest=b/name;assert root.is_dir();dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q);pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=src,destination=str(dest),bytes=sum(x['bytes'] for x in pins),pins=pins))
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters4-20261110')
for n in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/n,b/n)
for n in ['NMM_objects','NMM_tmp','NMM_target']:(b/n).mkdir(exist_ok=True)
(b/'NMM_tmp/.keep').touch()
print(json.dumps(dict(seeds=out,free_bytes=shutil.disk_usage(b).free)))
""".replace('BB',repr(B)).replace('SS',repr(sources))
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/'NMM_SEED.json').write_text(r.stdout)
env=json.loads((E.parent/'tx2-adapters4-20261110/NLK_ENV.json').read_text())
paths=json.loads((E.parent/'ledger24-20261110/NLX_PATHS.json').read_text())
env['LEAN_PATH']=':'.join(dict.fromkeys([B+'/NMM_objects']+[B+'/'+n for _,n in sources]+paths+env['LEAN_PATH'].split(':')))
env['TMPDIR']=B+'/NMM_tmp';env['CARGO_TARGET_DIR']=B+'/NMM_target'
(E/'NMM_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
print(json.dumps(dict(seed_bytes=sum(x['bytes'] for x in json.loads(r.stdout)['seeds']),free_bytes=json.loads(r.stdout)['free_bytes'])))
