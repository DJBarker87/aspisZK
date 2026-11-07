"""Read-only hash-pinned copy of NMX retained objects into LIB's own cache."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import subprocess,json,hashlib,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111')
with (b/'LIB_seedNMX-admission.log').open('w') as f:
 r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'LIB_seedNMX-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'LIB_seedNMX-admission.json').read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
source=Path('/home/dombarker/project-offloads/codex-cx-tx2-auth-20261111/NMX_objects')
dest=b/'LIB_seedNMX';dest.mkdir(exist_ok=True);rows=[]
for p in sorted(source.glob('NMX_*')):
 if not p.is_file() or not any(str(p).endswith(t) for t in ['.olean','.olean.private','.olean.server','.ir']):continue
 q=dest/p.name;h=hashlib.sha256(p.read_bytes()).hexdigest()
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==h
 rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
print(json.dumps(dict(admission=a,exit=0,objects=rows)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'LIB_seedNMX.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
(E/'LIB_NMX_OBJECT_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
p=E/'LIB_PATHS.json';x=json.loads(p.read_text());n='/home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_seedNMX'
if n not in x:x.insert(1,n)
p.write_text(json.dumps(x,indent=1)+'\n')
print('Copied and pinned NMX objects without modifying their cache')
