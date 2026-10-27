from pathlib import Path
import subprocess,json,base64
D=Path('evidence/pv-route2-20261027')
remote=r'''
from pathlib import Path
import json,base64,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-route2-20261027')
allowed={'target.json','receipt.json','refusal.json','admission-before.json','admission-barrier.json','reservation.log','output.log','time.log','submission.json','launcher.log','out.log'}
files={}
for p in D.iterdir():
 if p.is_dir() and (p.name.startswith('charon-') or p.name.startswith('aeneas-')) and (p/'target.json').exists():
  for q in p.iterdir():
   if q.is_file() and q.name in allowed:files[str(q.relative_to(D))]=base64.b64encode(q.read_bytes()).decode()
for p in (D/'lean-receipts').glob('*/*'):
 if p.is_file() and p.name in allowed:files[str(p.relative_to(D))]=base64.b64encode(p.read_bytes()).decode()
for name in ['TALLY.json','NEXT-ID.json']:
 p=D/name
 if p.exists():files[name]=base64.b64encode(p.read_bytes()).decode()
hashes={}
for p in D.glob('PV_R2*.llbc'):hashes[p.name]={'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
files['host-input-hashes.json']=base64.b64encode(json.dumps(hashes,indent=2).encode()).decode()
print(json.dumps(files))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=remote.encode(),stdout=subprocess.PIPE,check=True)
files=json.loads(r.stdout)
for name,data in files.items():
 p=D/name;assert p.resolve().is_relative_to(D.resolve());p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(base64.b64decode(data))
print('Fetched',len(files),'text evidence files; no cache, LLBC body, binary or object copied')
