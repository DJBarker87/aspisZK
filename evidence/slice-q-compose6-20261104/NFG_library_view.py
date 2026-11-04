from NFG_remote import *
assert not (E/'NFG_ACTIVE.json').exists()
a='NFG_PEER_STANDARD_IR_VIEW';admit(a)
r=ssh(a,'python3',f'''from pathlib import Path
import hashlib,json
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-q-compose6-cache-20261104');view=cache/'NFG_standard_view';view.mkdir(exist_ok=True)
roots=[Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')]
pins=[]
for name in ['Aeneas','Mathlib','Aesop','Batteries','Qq','ProofWidgets','ImportGraph','LeanSearchClient','Plausible','Lean','Init','Std']:
 for root in roots:
  targets=[root/name]+list(root.glob(name+'.*'))
  for src in targets:
   if not src.exists():continue
   dst=view/src.name
   if dst.exists():continue
   dst.symlink_to(src,target_is_directory=src.is_dir());pins.append(dict(view=str(dst),target=str(src)))
print(json.dumps(pins))
''');assert r.returncode==0,r.stderr
(E/'NFG_PEER_STANDARD_IR_VIEW.json').write_text(r.stdout)
