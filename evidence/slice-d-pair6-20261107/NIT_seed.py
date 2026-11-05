from pathlib import Path
import json,hashlib,shutil
B=Path('/home/dombarker/project-offloads/codex-cx-slice-d-pair6-20261107')
C=Path('/home/dombarker/project-offloads/codex-cx-slice-d-finish-cache-20261104')
a=json.loads((B/'NIT_SEED-admission.json').read_text());assert a['allowed'] is True
seed=B/'NIT_seed';seed.mkdir(exist_ok=True); pins={}
for src in [C/'NIQ_exports_20261107/objects',C/'NIG_exports_20261107/objects']:
 if not src.exists():continue
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  target=seed/p.relative_to(src)
  if target.exists():continue
  target.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,target)
  pins[str(target)]={'source':str(p),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size}
W=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py']:shutil.copy2(W/n,B/n)
print(json.dumps({'admission':a,'pins':pins,'seed_bytes':sum(v['bytes'] for v in pins.values()),'runner_pins':{n:hashlib.sha256((B/n).read_bytes()).hexdigest() for n in ['S2W_run_host.py','S2W_lean_host.py']}},indent=2))
