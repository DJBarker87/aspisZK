from pathlib import Path
import json,subprocess,lzma,hashlib
E=Path(__file__).resolve().parent
B='/home/dombarker/project-offloads/codex-cx-lib-20261111'
exports=[]
for folder,pre in [('ledger25-20261111','NMQ'),('tx2-owned-20261111','NMS_R2'),('model-bridge-20261111','NND')]:
 p=E.parent/folder/(pre+'_EXPORT.json')
 if p.exists():
  x=json.loads(p.read_text())
  if 'files' in x:exports.append(x)
code='''from pathlib import Path
import shutil,subprocess,json,hashlib,lzma,sys
b=Path(B);b.mkdir(exist_ok=True)
with (b/'LIB_seed-admission.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'LIB_seed-admission.json')],stdout=f,stderr=subprocess.STDOUT)
p=b/'LIB_seed-admission.json';assert p.exists(),'missing admission'
a=json.loads(p.read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
rows=[]
for i,ex in enumerate(exports):
 root=ex.get('export',ex.get('path',ex.get('directory')))
 for row in ex['files']:
  p=Path(row.get('path',str(root)+'/'+row.get('name','')));h=hashlib.sha256(p.read_bytes()).hexdigest();assert h==row['sha256'],str(p)
  q=b/('LIB_seed'+str(i))/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
x=dict(files=rows,admission=a,exit=r.returncode,disk=shutil.disk_usage(b)._asdict())
(b/'LIB_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(x))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input='B='+repr(B)+'\nexports='+repr(exports)+'\n'+code,capture_output=True,text=True)
(E/'LIB_SETUP.log').write_text(r.stdout+r.stderr)
assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);(E/'LIB_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()))
p=E/'LIB_PATHS.json';paths=[B+'/LIB_seed'+str(i) for i in range(len(exports))]+json.loads(p.read_text());p.write_text(json.dumps(paths,indent=1)+'\n')
print(json.dumps(dict(copied=len(x['files']),bytes=sum(z['bytes']for z in x['files']),free=x['disk']['free'])))
