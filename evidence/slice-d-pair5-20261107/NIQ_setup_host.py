from pathlib import Path
import subprocess,json,hashlib,shutil,sys
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair5-20261107')
W=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104')
B.mkdir(exist_ok=True)
with (B/'NIQ_SETUP-barrier.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(B/'NIQ_SETUP-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=B/'NIQ_SETUP-admission.json'
ad=json.loads(p.read_text()) if p.exists() else {}
if r.returncode or ad.get('allowed') is not True:
 print(json.dumps(dict(exit=r.returncode,reservation=ad)));sys.exit(78)
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(W/n,B/n)
for n in ['NIQ_objects','NIQ_generated','NIQ_seed','NIQ_tmp','NIQ_native']:(B/n).mkdir(exist_ok=True)
rows=[]
for p in sorted((C/'NIG_exports_20261107/objects').iterdir()):
 if p.is_file():
  dest=B/'NIQ_seed'/p.name;shutil.copy2(p,dest)
  rows.append(dict(source=str(p),path=str(dest),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
receipt=dict(admission=ad,exit=0,files=rows,seed_bytes=sum(r['bytes'] for r in rows),method='COPY retained NIG export; other coherent cache objects read-only')
(B/'NIQ_SEED.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt))
