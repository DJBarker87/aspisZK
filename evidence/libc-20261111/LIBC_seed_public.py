from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json
s=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_exports_A_20261111');d=Path('/home/dombarker/project-offloads/codex-cx-libc-20261111/LIBC_base');pins=[]
p=s/'LIB_VPublicDomain.olean';assert p.exists()
for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
 if z.is_file():
  q=d/z.name
  if q.exists():assert q.read_bytes()==z.read_bytes()
  else:shutil.copy2(z,q)
  pins.append({'source':str(z),'destination':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()})
print(json.dumps(pins,indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'LIBC_PUBLIC_PINS.json').write_text(r.stdout)
print('Pinned retained LIB_VPublicDomain object')
