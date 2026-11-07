from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
modules=[]
for p in sorted(E.glob('LIBC_L[0-9][0-9][0-9]/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit_status']==0 and j['kind']=='lean' and not j['module'].startswith('LIBC_Inspect'):modules.append(j['module'])
modules=sorted(set(modules))
code='''from pathlib import Path
import hashlib,shutil,json
b=Path('/home/dombarker/project-offloads/codex-cx-libc-20261111');out=b/'LIBC_exports_20261111';pins=[]
for n in MODULES:
 p=b/'LIBC_objects'/(n.replace('.','/')+'.olean')
 assert p.exists(),n
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if z.is_file():
   q=out/z.relative_to(b/'LIBC_objects');q.parent.mkdir(parents=True,exist_ok=True)
   if q.exists():assert q.read_bytes()==z.read_bytes()
   else:shutil.copy2(z,q)
   pins.append({'module':n,'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest(),'bytes':q.stat().st_size})
print(json.dumps({'directory':str(out),'modules':MODULES,'files':pins},indent=1))
'''.replace('MODULES',repr(modules))
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'LIBC_EXPORT.json').write_text(r.stdout)
print('Retained private export',len(modules),'modules')
