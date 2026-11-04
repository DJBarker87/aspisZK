"""Retain accepted objects first; remove only this job's rebuildable scratch."""
from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
code=r'''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-slice-s-compose12-20261104')
checks=[]
for p in b.glob('NFJ_[KL]*/receipt.json'):
 r=json.loads(p.read_text());cg=Path('/sys/fs/cgroup')/r['cgroup'].lstrip('/')
 if cg.exists():
  text=(cg/'cgroup.events').read_text();assert 'populated 0' in text
  checks.append(dict(cgroup=str(cg),events=text))
cache=b.parent/'codex-cx-slice-s-compose12-cache-20261104/NFJ_final_objects_20261104';pins=[]
for p in (b/'NFJ_objects').rglob('*'):
 if not p.is_file():continue
 dst=cache/p.relative_to(b/'NFJ_objects');dst.parent.mkdir(parents=True,exist_ok=True)
 h=hashlib.sha256(p.read_bytes()).hexdigest()
 if dst.exists():assert hashlib.sha256(dst.read_bytes()).hexdigest()==h
 else:shutil.copy2(p,dst)
 pins.append(dict(source=str(p),destination=str(dst),sha256=h,bytes=p.stat().st_size))
binary=b/'NFJ_native/NFJ_Driver';binary_pin=dict(path=str(binary),sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),bytes=binary.stat().st_size)
removed=[]
for name in ['NFJ_target','NFJ_tmp','NFJ_objects']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
# Retain exact C/Lean sources and receipts; the executable is rebuildable.
binary.unlink();removed.append(str(binary))
print(json.dumps(dict(all_own_scopes_terminal=True,populated_checks=checks,retained_cache=str(cache),accepted_object_pins=pins,binary=binary_pin,removed_only_own_scratch=removed,cache_deleted=False),indent=1))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'NFJ_CLEANUP.json').write_text(r.stdout);print('Accepted cache retained; own rebuildable scratch removed')
