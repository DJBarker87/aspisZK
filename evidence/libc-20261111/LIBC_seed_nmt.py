from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json
s=Path('/home/dombarker/project-offloads/codex-cx-tx1-owned-20261111/NMT_exports_20261111');d=Path('/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_seedNMT');pins={}
for p in s.rglob('*'):
 if p.is_file():
  q=d/p.relative_to(s);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  pins[str(q)]={'source':str(p),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()}
print(json.dumps(pins))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'LIBC_NMT_PINS.json').write_text(r.stdout)
p=E/'LIBC_PATHS.json';paths=json.loads(p.read_text());n='/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_seedNMT'
if n not in paths:paths.insert(3,n)
p.write_text(json.dumps(paths,indent=2)+'\n')
print('Copied and pinned',len(json.loads(r.stdout)),'NMT objects')
