"""Seed only this job's scratch/cache; existing launchers copied byte-identically."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import shutil,hashlib,json,subprocess
root=Path('/home/dombarker/project-offloads');b=root/'codex-cx-slice-s-compose4-20261029';b.mkdir(exist_ok=True)
old=root/'codex-cx-slice-s-compose3-20261029'
pins=[]
for name in ['S2W_run_host.py']:
 p=old/name;q=b/name
 if not q.exists():shutil.copy2(p,q)
 assert p.read_bytes()==q.read_bytes()
 pins.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
s=b/'NEL_src'
if not s.exists():
 shutil.copytree(old/'NEJ_src',s)
 for n in ['NEJ_contracts_applied.patch','NEJ_oracle.patch','NEJ_contract_controls.patch','NEJ_KMX_copy_stubs.patch']:
  subprocess.run(['git','apply','--reverse',str(old/n)],cwd=s,check=True,capture_output=True)
 # Frozen uploaded corpus pins are checked before own cfg-only patches.
cache=root/'codex-cx-slice-s-compose4-cache-20261029';cache.mkdir(exist_ok=True)
seeds=['codex-cx-slice-s-compose3-cache-20261029/NEJ_final_objects_20261101','codex-cx-slice-s-compose3-cache-20261029','codex-cx-leaf-cache-20261027','codex-cx-cpilot-cache-20261028','codex-cx-front2-cache-20261028','codex-cx-front4-cache-20261028','codex-cx-slice-s-compose2-cache-20261029','codex-cx-slice-s-compose-cache-20261029']
for seed in seeds:
 r=root/seed
 if not r.exists():continue
 for p in r.rglob('*'):
  if not p.is_file() or p.suffix not in ['.olean','.lean','.ilean']:continue
  # Seed top-level module layout, with NEJ accepted objects first.
  rel=p.relative_to(r);q=cache/rel
  if q.exists():continue
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
  pins.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(dict(imports=pins)))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'NEL_BOOTSTRAP.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
(E/'NEL_HOST_PINS.json').write_text(r.stdout)
