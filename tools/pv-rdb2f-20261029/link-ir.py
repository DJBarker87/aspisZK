from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');j=json.loads((D/'preflight.json').read_text());rows=[]
for r in j['reuse']:
 p=Path(r['path']);assert hashlib.sha256(p.read_bytes()).hexdigest()==r['object_sha256']
 for suffix in ['.ir']:
  s=p.with_suffix(suffix)
  if s.exists():
   dest=D/'lean-objects'/(r['module'].replace('.','/')+suffix);assert not dest.exists();dest.symlink_to(s);rows.append(dict(module=r['module'],path=str(s),sha256=hashlib.sha256(s.read_bytes()).hexdigest()))
(D/'ir-pins.json').write_text(json.dumps(rows,indent=2));print('Verified parent object and linked',len(rows),'original sidecars')
