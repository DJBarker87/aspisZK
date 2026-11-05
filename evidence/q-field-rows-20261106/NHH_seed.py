from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-q-field-rows-20261106'
code='''from pathlib import Path
import json,shutil,hashlib,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-q-field-rows-20261106');b.mkdir(exist_ok=True)
with (b/'NHH_seed-reservation.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHH_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'NHH_seed-admission.json';a=json.loads(p.read_text()) if p.exists() else {};print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(0 if r.returncode==0 and a.get('allowed') is True else 78)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,text=True,capture_output=True);(E/'NHH_SEED_ADMISSION.json').write_text(r.stdout);assert r.returncode==0,r.stderr
code='''from pathlib import Path
import shutil,json,hashlib
b=Path('/home/dombarker/project-offloads/codex-cx-q-field-rows-20261106');c=Path('/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104/NHH_seed_20261106');c.mkdir(exist_ok=True)
roots=[('/home/dombarker/project-offloads/codex-cx-slice-d-field3-cache-20261104/NGH_exports_20261105','NGH'),('/home/dombarker/project-offloads/codex-cx-slice-q-accum-cache-20261104/NFS_exports_20261104','NFS'),('/home/dombarker/project-offloads/codex-cx-pool-retarget-cache-20261104/NGK_exports_20261105','NGK')]
out=[]
for root,label in roots:
 for p in Path(root).rglob('*'):
  if p.is_file() and not p.name.endswith('.c'):
   q=c/label/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q);out.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 p=b.parent/'codex-cx-sound-int2-20261025'/n;shutil.copyfile(p,b/n);out.append(dict(source=str(p),destination=str(b/n),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
for n in ['NHH_objects','NHH_tmp','NHH_native','NHH_src']:(b/n).mkdir(exist_ok=True)
print(json.dumps(dict(files=out,seed_bytes=sum(x['bytes'] for x in out))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr;(E/'NHH_CACHE_IMPORTS.json').write_text(r.stdout);print(json.loads(r.stdout)['seed_bytes'])
