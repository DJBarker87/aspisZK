from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent
code=r'''
from pathlib import Path
import subprocess,json,hashlib,shutil,sys
root=Path('/home/dombarker/project-offloads'); b=root/'codex-cx-pool-retdata3-20261104'; b.mkdir(exist_ok=True)
q=b/'NFV_SETUP-admission.json'
with (b/'NFV_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3',str(root/'codex-cx-s2h-20261023/S2H_reservation.py'),str(q)],stdout=f,stderr=subprocess.STDOUT)
print((b/'NFV_SETUP-barrier.log').read_text(),file=sys.stderr)
if r.returncode or not q.exists() or json.loads(q.read_text()).get('allowed') is not True:sys.exit(78)
old=root/'codex-cx-pool-retdata2-cache-20261104'; cache=root/'codex-cx-pool-retdata3-cache-20261104';cache.mkdir(exist_ok=True);records=[]
for origin in [old/'NFR_final_objects_20261104',old/'NFR_audit_native_20261104',old]:
 for p in origin.rglob('*'):
  if not p.is_file():continue
  dst=cache/p.relative_to(old)
  if dst.exists():continue
  dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
  records.append(dict(source=str(p),destination=str(dst),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size=p.stat().st_size))
shutil.copy2(root/'codex-cx-pool-retdata2-20261104/S2W_run_host.py',b/'S2W_run_host.py')
for n in ['NFV_objects','NFV_tmp']:(b/n).mkdir(exist_ok=True)
print(json.dumps(dict(imports=records,admission=json.loads(q.read_text()),launcher_sha256=hashlib.sha256((b/'S2W_run_host.py').read_bytes()).hexdigest())))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFV_SETUP.log').write_text(r.stderr)
if r.returncode:raise SystemExit(r.returncode)
(E/'NFV_HOST_PINS.json').write_text(r.stdout)
print('Imported',len(json.loads(r.stdout)['imports']),'objects and retained artifacts')
