"""Materialize only preflight-verified unaffected objects in this task's prefix."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');j=json.loads((D/'preflight.json').read_text())
for r in j['reuse']:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256'];dest=D/'lean-objects'/(r['module'].replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True);assert not dest.exists();dest.symlink_to(p)
print('Linked',len(j['reuse']),'verified unaffected objects; no affected cached object linked')
