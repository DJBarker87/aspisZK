from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-row-bridges-20261109'
exports=['/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NKW_20261109/NKW_exports_20261109','/home/dombarker/project-offloads/codex-cx-terminal4-20261108/NKI_exports_20261108','/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_exports_final_20261108']
code='''from pathlib import Path
import json,subprocess,shutil,hashlib,sys
b=Path(B); b.mkdir(exist_ok=True)
with (b/'NKY_seed-admission.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NKY_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NKY_seed-admission.json'
assert p.exists(),'missing admission'
a=json.loads(p.read_text())
if r.returncode or a.get('allowed') is not True: print(json.dumps(a));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
rows=[];paths=[]
for i,root in enumerate(exports):
 q=b/('NKY_seed'+str(i));q.mkdir(exist_ok=True);paths.append(str(q))
 for p in Path(root).rglob('*'):
  if not p.is_file():continue
  d=q/p.relative_to(root);d.parent.mkdir(parents=True,exist_ok=True)
  old=hashlib.sha256(p.read_bytes()).hexdigest();shutil.copy2(p,d)
  assert hashlib.sha256(d.read_bytes()).hexdigest()==old
  rows.append(dict(source=str(p),destination=str(d),sha256=old,bytes=p.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
for n in ['NKY_objects','NKY_tmp','NKY_target']: (b/n).mkdir(exist_ok=True)
obj=dict(files=rows,bytes=sum(r['bytes']for r in rows),admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict(),paths=paths)
(b/'NKY_CACHE_IMPORTS.json.xz').write_bytes(__import__('lzma').compress(json.dumps(obj).encode()))
print(json.dumps(obj))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nexports='+repr(exports)+'\n'+code,text=True,capture_output=True)
(E/'NKY_setup.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,(r.returncode,r.stdout[-1000:],r.stderr)
x=json.loads(r.stdout);(E/'NKY_SEED.json').write_text(json.dumps(x,indent=1)+'\n')
paths=x['paths']+json.loads((E.parent/'ledger20-20261109/NKW_PATHS.json').read_text())
(E/'NKY_PATHS.json').write_text(json.dumps(paths,indent=1)+'\n')
print(json.dumps(dict(files=len(x['files']),bytes=x['bytes'],free=x['disk']['free'])))
