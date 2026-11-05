from pathlib import Path
import subprocess,json,lzma
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,json,shutil,hashlib,lzma,sys
b=Path('/home/dombarker/project-offloads/codex-cx-l159-physical-20261107');b.mkdir(exist_ok=True)
with (b/'NIN_SEED_BARRIER.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIN_SEED_ADMISSION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NIN_SEED_ADMISSION.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=a)),flush=True)
if r.returncode or a.get('allowed')is not True:sys.exit(78)
c=Path('/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NIN_20261107');c.mkdir(exist_ok=True)
rows=[]
for source in ['/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat/NIM_exports_20261107','/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGP_exports_20261105','/home/dombarker/project-offloads/codex-cx-carriers-bind-cache-20261104/NGK_exports_20261105']:
 for p in Path(source).rglob('*'):
  if p.is_file():
   q=c/p.relative_to(source);q.parent.mkdir(parents=True,exist_ok=True)
   if not q.exists():shutil.copy2(p,q)
   assert hashlib.sha256(p.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest()
   rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(selected=rows,logical_bytes=sum(x['bytes']for x in rows),admission=a,exit=r.returncode)
(b/'NIN_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NIN_SEED.log').write_text(r.stdout+r.stderr);print(r.stdout[-500:],r.stderr);assert r.returncode==0
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','cat /home/dombarker/project-offloads/codex-cx-l159-physical-20261107/NIN_CACHE_IMPORTS.json.xz'],capture_output=True);assert r.returncode==0;(E/'NIN_CACHE_IMPORTS.json.xz').write_bytes(r.stdout)
