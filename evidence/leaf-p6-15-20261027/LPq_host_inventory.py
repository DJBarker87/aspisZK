from pathlib import Path
import subprocess,json,shlex
H='dombarker@100.108.41.90'; E=Path(__file__).resolve().parent
script='''from pathlib import Path
import json,hashlib
base=Path('/home/dombarker/project-offloads')
roots=[base/'codex-cx-sound-int2-20261025',base/'codex-cx-sound-int2-20261025/objects',base/'codex-cx-assoc-a2-cache-20261027/XRw_objects',base/'codex-cx-leaf-p6-11-20261027/LPm_objects']
out={'roots':{},'selected':{}}
for root in roots:
 if root.exists():
  names={str(p.relative_to(root)):dict(path=str(p),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in root.rglob('*.olean') if p.name.startswith(('LPm_','LPi_','LPf_','LPn_','XRy_'))}
  out['roots'][str(root)]=names
for root in roots[:1]:
 for p in root.rglob('Aeneas.olean'):
  out['selected'][str(p)]=dict(bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(out))
'''
r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -c '+shlex.quote(script)],capture_output=True,text=True)
(E/'LPq_inventory-transport.log').write_text(r.stderr)
if r.returncode:raise SystemExit(r.returncode)
(E/'LPq_HOST_INVENTORY.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print({root:len(xs) for root,xs in json.loads(r.stdout)['roots'].items()})
