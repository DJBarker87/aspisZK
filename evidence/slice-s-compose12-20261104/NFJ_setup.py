"""Own workspace/cache; read-only cache origins; existing host runner unchanged."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose12-20261104');b.mkdir(exist_ok=True)
q=b/'NFJ_SETUP-reservation.json'
with (b/'NFJ_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/'NFJ_SETUP-barrier.log').read_text(),file=sys.stderr,flush=True)
if r.returncode!=0 or json.loads(q.read_text()).get('allowed') is not True:sys.exit(78)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
cache=b.parent/'codex-cx-slice-s-compose12-cache-20261104';cache.mkdir(exist_ok=True);records=[]
origins=[b.parent/'codex-cx-slice-s-compose11-cache-20261104/NFH_final_objects_20261104',b.parent/'codex-cx-slice-s-compose11-cache-20261104',b.parent/'codex-cx-slice-s-compose10-cache-20261029/NFD_final_objects_20261104',b.parent/'codex-cx-slice-s-compose9-cache-20261029/NEY_final_objects_20261104']
for label,date in [('slice-s-compose10','20261029'),('leaf','20261027'),('cpilot','20261028'),('front2','20261028'),('front4','20261028'),('slice-s-compose9','20261029'),('slice-s-compose8','20261029'),('slice-s-compose7','20261029'),('slice-s-compose6','20261029'),('slice-s-compose5','20261029'),('slice-s-compose4','20261029'),('slice-s-compose3','20261029'),('slice-s-compose2','20261029'),('slice-s-compose','20261029')]:origins.append(b.parent/('codex-cx-'+label+'-cache-'+date))
for src in origins:
 if not src.exists():continue
 for p in src.rglob('*'):
  if not p.is_file() or p.suffix not in ['.olean','.lean']:continue
  dst=cache/p.relative_to(src)
  if dst.exists():continue
  dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst);records.append(dict(source=str(p),destination=str(dst),sha256=sha(p),size=p.stat().st_size))
old=b.parent/'codex-cx-slice-s-compose10-20261029'
assert not (b/'NFJ_HOST_PINS_corrected.json').exists(),'setup already performed'
shutil.copy2(old/'S2W_run_host.py',b/'S2W_run_host.py')
(b/'NFJ_objects').mkdir(exist_ok=True)
pins=dict(imports=records,admission=json.loads(q.read_text()),launcher_sha256=sha(b/'S2W_run_host.py'))
(b/'NFJ_HOST_PINS.json').write_text(json.dumps(pins,indent=1))
print(json.dumps(pins))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFJ_SETUP.log').write_text(r.stderr)
if r.returncode:print(r.stderr);raise SystemExit(r.returncode)
(E/'NFJ_HOST_PINS.json').write_text(r.stdout)
print('Imported',len(json.loads(r.stdout)['imports']),'cache files; runner copied unchanged')
