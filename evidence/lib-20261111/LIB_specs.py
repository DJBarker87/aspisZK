from pathlib import Path
import hashlib,json,lzma,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'tx2-owned-20261111'
closure=json.loads(lzma.decompress((P/'NMS_R2_CLOSURE_PINS.json.xz').read_bytes()))
objects=[o for m in closure if m['module'].startswith('RSL_') for o in m['objects'] if '/NMS_R2_RSL_objects/'in o['path']]
source=[]
for i in range(282,289):
 x=json.loads((P/f'NMS_L{i:03}/receipt.json').read_text());assert x['exit_status']==0
 for n,h in x['source_hashes'].items():
  if not n.endswith('.lean'):continue
  p=E.parent/'rowspec-lead-20261107'/Path(n).name;assert hashlib.sha256(p.read_bytes()).hexdigest()==h
  source.append(dict(path=str(p),sha256=h,receipt=f'NMS_L{i:03}'))
code='''from pathlib import Path
import hashlib,json,subprocess,shutil,sys
b=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111')
with (b/'LIB_specs-admission.log').open('w')as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(b/'LIB_specs-admission.json')],stdout=f,stderr=subprocess.STDOUT)
a=json.loads((b/'LIB_specs-admission.json').read_text())
if r.returncode or a.get('allowed')is not True:print(json.dumps(dict(exit=r.returncode,reservation=a)));sys.exit(78)
assert shutil.disk_usage(b).free>=40_000_000_000
rows=[]
for row in objects:
 p=Path(row['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==row['sha256']
 q=b/'LIB_specs'/p.name;q.parent.mkdir(exist_ok=True)
 if not q.exists():shutil.copy2(p,q)
 assert hashlib.sha256(q.read_bytes()).hexdigest()==row['sha256']
 rows.append(dict(row,destination=str(q)))
print(json.dumps(dict(files=rows,admission=a,exit=r.returncode)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input='objects='+repr(objects)+'\n'+code,text=True,capture_output=True);(E/'LIB_SPECS.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stdout+r.stderr
(E/'LIB_SPEC_PINS.json').write_text(json.dumps(dict(source=source,**json.loads(r.stdout)),indent=1)+'\n')
p=E/'LIB_PATHS.json';x=json.loads(p.read_text());p.write_text(json.dumps(['/home/dombarker/project-offloads/codex-cx-lib-20261111/LIB_specs']+x,indent=1)+'\n')
print('Copied canonical RSL rev2 objects; matching source receipts verified')
