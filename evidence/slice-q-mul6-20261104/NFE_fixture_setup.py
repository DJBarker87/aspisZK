from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-q-mul6-20261029';C=P/'codex-cx-slice-q-mul6-cache-20261029/fixtures'
with (B/'NFE_fixture_barrier.log').open('w') as f:r=subprocess.run(['python3',str(P/'codex-cx-s2h-20261023/S2H_reservation.py'),str(B/'NFE_fixture_admission.json')],stdout=f,stderr=subprocess.STDOUT)
ad=json.loads((B/'NFE_fixture_admission.json').read_text());print(json.dumps(dict(exit=r.returncode,reservation=ad)),flush=True)
if r.returncode!=0 or ad.get('allowed') is not True:sys.exit(78)
C.mkdir(exist_ok=True);pins=[]
for m in ['NEP_Planted','NEP_Mutations']:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=P/'codex-pv-evhc9-20261104'/(m+suffix)
  if not p.is_file():continue
  q=C/p.name;shutil.copyfile(p,q);h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==hashlib.sha256(q.read_bytes()).hexdigest()
  pins.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(pins))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
(E/'NFE_FIXTURE_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
lines=r.stdout.splitlines();(E/'NFE_FIXTURE_ADMISSION.json').write_text(lines[0]);(E/'NFE_FIXTURE_IMPORTS.json').write_text(lines[-1]);print('fixtures copied with admission')
