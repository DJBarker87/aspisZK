from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,shutil,hashlib,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-q-leftovers-20261106'); b.mkdir(exist_ok=True)
with (b/'NHN_seed-reservation.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NHN_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NHN_seed-admission.json').read_text());assert r.returncode==0 and a.get('allowed') is True
out=[]
for n in ['S2W_run_host.py','S2W_lean_host.py']:
 p=b.parent/'codex-cx-sound-int2-20261025'/n;q=b/n;shutil.copyfile(p,q);out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for d in ['NHN_objects','NHN_tmp','NHN_native','NHN_src']:(b/d).mkdir(exist_ok=True)
s=b.parent/'codex-cx-q-field-rows-20261106'/'NHH_src'
for p in s.iterdir():
 q=b/'NHN_src'/p.name
 if not q.exists():q.symlink_to(p,target_is_directory=p.is_dir())
# Keep the reusable corpus read-only: only the harness crate is copied.
for n in ['crates','crates/aspis-r1-cost-probe','crates/aspis-r1-cost-probe/src']:
 q=b/'NHN_src'/n
 if q.is_symlink():q.unlink();q.mkdir()
 for p in (s/n).iterdir():
  t=q/p.name
  if not t.exists():t.symlink_to(p,target_is_directory=p.is_dir())
for n in ['crates/aspis-r1-cost-probe/src/lib.rs']:
 q=b/'NHN_src'/n
 if q.is_symlink():q.unlink()
# Small object-only seed, retained in assigned cache.
c=b.parent/'codex-cx-slice-d-field3-cache-20261104';src=c/'NHH_exports_final_20261106/objects';dst=c/'NHN_seed_20261106';dst.mkdir(exist_ok=True)
for p in src.iterdir():
 q=dst/p.name;shutil.copyfile(p,q);out.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(dict(admission_exit=r.returncode,reservation=a,files=out,seed_bytes=sum(x['bytes'] for x in out))))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NHN_SEED.json').write_text(r.stdout);assert r.returncode==0,r.stderr
print('Seed bytes',json.loads(r.stdout)['seed_bytes'])
