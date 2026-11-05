from pathlib import Path
import json,subprocess
E=Path(__file__).resolve().parent;x=json.loads((E.parent/'slice-d-entry4-20261106/NHY_CACHE_EXPORT.json').read_text())
code='''from pathlib import Path
import json,hashlib,shutil,subprocess,sys
b=Path('/home/dombarker/project-offloads/codex-cx-owner-dedupe-20261107');c=Path('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NIM_flat')
with (b/'NIM_SUPPLEMENT_BARRIER.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'NIM_SUPPLEMENT_ADMISSION.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'NIM_SUPPLEMENT_ADMISSION.json').read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
rows=[]
for f in x['files']:
 p=Path(x['directory'])/f['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==f['sha256']
 for z in [p,Path(str(p)+'.private'),Path(str(p)+'.server'),p.with_suffix('.ir')]:
  if not z.exists():continue
  q=c/f['path'];q=q.parent/z.name;q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(z.read_bytes()).hexdigest()
  if q.exists():assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  else:shutil.copy2(z,q)
  rows.append(dict(source=str(z),destination=str(q),sha256=h,bytes=q.stat().st_size))
y=dict(files=rows,bytes=sum(r['bytes']for r in rows),admission=a,exit=r.returncode);(b/'NIM_SUPPLEMENT.json').write_text(json.dumps(y));print(json.dumps(y))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='x='+repr(x)+'\n'+code,text=True,capture_output=True);(E/'NIM_SUPPLEMENT.json').write_text(r.stdout);(E/'NIM_SUPPLEMENT.stderr').write_text(r.stderr);print(r.returncode,r.stdout[-350:],r.stderr);assert r.returncode==0
