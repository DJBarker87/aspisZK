from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());roots=list(map(Path,e['LEAN_PATH'].split(':')))
manifest=json.loads((D/'external-object-manifest.json').read_text());checks=[]
for x in manifest:
 rel=x['module']+'.olean'; p=next((r/rel for r in roots if (r/rel).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 checks.append(dict(module=x['module'],selected_path=str(p),expected=x['object_sha256'],actual=h,ok=h==x['object_sha256']))
j=dict(ok=all(x['ok'] for x in checks),checks=checks,errors=[x for x in checks if not x['ok']],env=e)
(D/'preflight.json').write_text(json.dumps(j,indent=2));print(json.dumps(dict(ok=j['ok'],checked=len(checks),errors=j['errors'])))
