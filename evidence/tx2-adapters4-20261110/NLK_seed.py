from NLK_transport import *
import hashlib
admission('NLK_P001')
sources=[('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014','NLK_NLF_seed'),('/home/dombarker/project-offloads/codex-cx-tx2-adapters3-20261109/NLA_exports_final_20261109','NLK_NLA_seed'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLG_20261110/NLG_exports_20261110','NLK_NLG_seed')]
code="""from pathlib import Path
import shutil,json,hashlib
b=Path(BB);out=[]
for src,name in SS:
 root=Path(src);dest=b/name;assert root.is_dir();dest.mkdir(exist_ok=True);pins=[]
 for p in sorted(root.rglob('*')):
  if p.is_file():
   q=dest/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);assert not q.exists();shutil.copy2(p,q);pins.append(dict(relative=str(p.relative_to(root)),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
 out.append(dict(source=src,destination=str(dest),bytes=sum(x['bytes'] for x in pins),pins=pins))
src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters3-20261109')
for n in ['S2W_run_host.py','lakefile.lean']:shutil.copy2(src/n,b/n)
for n in ['NLK_objects','NLK_tmp','NLK_target']:(b/n).mkdir(exist_ok=True)
(b/'NLK_tmp/.keep').touch()
print(json.dumps(dict(seeds=out,free_bytes=shutil.disk_usage(b).free)))
""".replace('BB',repr(B)).replace('SS',repr(sources))
r=ssh('python3',code);assert r.returncode==0,r.stderr
(E/'NLK_SEED.json').write_text(r.stdout)
env=json.loads((E.parent/'sdk-borrow-20261109/NLF_L078.json').read_text())['env']
paths=json.loads((E.parent/'ledger21-20261110/NLG_PATHS.json').read_text())
env['LEAN_PATH']=':'.join(dict.fromkeys([B+'/NLK_objects']+[B+'/'+n for _,n in sources]+paths+env['LEAN_PATH'].split(':')))
env['TMPDIR']=B+'/NLK_tmp';env['CARGO_TARGET_DIR']=B+'/NLK_target'
(E/'NLK_ENV.json').write_text(json.dumps(env,indent=1)+'\n')
print(json.dumps(dict(seed_bytes=sum(x['bytes'] for x in json.loads(r.stdout)['seeds']),free_bytes=json.loads(r.stdout)['free_bytes'])))
