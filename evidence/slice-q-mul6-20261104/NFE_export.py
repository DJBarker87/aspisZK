from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
mods=[json.loads(p.read_text())['module'] for p in E.glob('NFE_L*/receipt.json') if json.loads(p.read_text())['kind']=='lean' and json.loads(p.read_text())['exit_status']==0]
code='''from pathlib import Path
import shutil,json,hashlib
P=Path('/home/dombarker/project-offloads');B=P/'codex-cx-slice-q-mul6-20261029';C=P/'codex-cx-slice-q-mul6-cache-20261029/NFE_exports_20261104';C.mkdir(exist_ok=True)
out=[]
for m in MODULES:
 for suffix in ['.olean','.olean.private','.olean.server','.ir']:
  p=B/'NFE_objects'/(m+suffix)
  if not p.is_file():continue
  q=C/p.name
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copyfile(p,q)
  out.append(dict(module=m,source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
print(json.dumps(out))
'''.replace('MODULES',repr(sorted(mods)))
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NFE_EXPORT_TRANSPORT.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
(E/'NFE_EXPORTS.json').write_text(r.stdout)
print('retained',len(json.loads(r.stdout)),'object/sidecar pins')
