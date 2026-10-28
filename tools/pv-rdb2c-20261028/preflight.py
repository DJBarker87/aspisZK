from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028')
e=json.loads(Path('/home/dombarker/project-offloads/codex-pv-rdb2-20261028/env-J.json').read_text())
e['LEAN_PATH']=e['LEAN_PATH'].replace('codex-pv-rdb2-20261028/lean-objects','codex-pv-rdb2c-20261028/lean-objects')
(D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True);(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
(D/'env-J.json').write_text(json.dumps(e,indent=2))
manifest=json.loads((D/'external.json').read_text());checks=[]
for r in manifest:
 m=r['module'];rel=m.replace('.','/')+'.olean';p=next((Path(d)/rel for d in e['LEAN_PATH'].split(':') if (Path(d)/rel).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 checks.append(dict(module=m,path=str(p),expected=r['object_sha256'],actual=h,ok=h==r['object_sha256']))
j=dict(ok=all(r['ok'] for r in checks),checks=checks,errors=[r for r in checks if not r['ok']],env=e)
(D/'preflight.json').write_text(json.dumps(j,indent=2));print(json.dumps(dict(ok=j['ok'],count=len(checks),errors=j['errors'])))
assert j['ok']
