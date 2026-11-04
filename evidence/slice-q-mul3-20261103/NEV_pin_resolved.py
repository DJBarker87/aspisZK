"""Read-only recovery of all resolved Aeneas pins and cohort selection."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib
B=Path('/home/dombarker/project-offloads/codex-cx-slice-q-mul3-20261029')
result=[]
for p in sorted(B.glob('NEV_L[0-9][0-9][0-9]/receipt.json')):
 x=json.loads(p.read_text());roots=[Path(v) for v in x['env']['LEAN_PATH'].split(':')]
 names=set()
 for root in roots:
  for name in ['Aeneas','AeneasMeta']:
   if (root/(name+'.olean')).is_file():names.add(name+'.olean')
   if (root/name).is_dir():
    names.update(str(p.relative_to(root)) for p in (root/name).rglob('*') if p.is_file() and any(str(p).endswith(v) for v in ['.olean','.olean.private','.olean.server','.ir']))
 pins=[]
 for name in sorted(names):
  p=next(root/name for root in roots if (root/name).is_file())
  pins.append(dict(module_file=name,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
 extras=[]
 for name in ['AspisR1PublicPreparation/Types.olean','S1SemanticPhaseV1.olean']:
  p=next((root/name for root in roots if (root/name).is_file()),None)
  if p:extras.append(dict(module_file=name,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 result.append(dict(attempt=x['attempt'],receipt_sha256=hashlib.sha256((B/x['attempt']/'receipt.json').read_bytes()).hexdigest(),resolved_library=pins,cohort=extras,read_only_recovery=True))
print(json.dumps(result,indent=2))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,capture_output=True,text=True)
assert r.returncode==0,r.stderr
(E/'NEV_RESOLVED_LIBRARY_PINS.json').write_text(r.stdout)
print('pinned',len(json.loads(r.stdout)),'attempts')
