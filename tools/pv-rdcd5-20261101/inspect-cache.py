from pathlib import Path
import json,hashlib
plan=json.load(__import__('sys').stdin)
base=Path('/home/dombarker/project-offloads');dirs=[base/'codex-pv-dlib-20261028',base/'codex-pv-alib-20261027',base/'codex-pv-rdcd3-20261028',base/'codex-cx-prover-rw-20261023']
out={}
for d in dirs:
 hits={}
 for m,x in plan['modules'].items():
  for root in [d/'lean-objects',d/'objects',d/'src/.lake/build/lib/lean']:
   p=root/(m.replace('.','/')+'.olean')
   if p.exists():hits[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
 out[str(d)]=hits
print(json.dumps(out,indent=2))
