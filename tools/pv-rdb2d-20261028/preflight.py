from pathlib import Path
import json,hashlib,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2c-20261028')
e=json.loads((D/'env-J.json').read_text()); roots=list(map(Path,e['LEAN_PATH'].split(':')))
checks=[]
for r in json.loads((D/'external.json').read_text()):
 rel=r['module'].replace('.','/')+'.olean';p=next((d/rel for d in roots if (d/rel).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 checks.append(dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=h,ok=h==r['object_sha256']))
collisions=[]
for d in D.parent.glob('codex-pv-*'):
 for p in d.glob('lean-61[0-0][0-9][0-9]'):
  collisions.append(str(p))
 for p in d.glob('**/sent.txt'):
  for line in p.read_text(errors='replace').splitlines():
   if re.search(r'\b610\d\d\b',line):collisions.append(dict(path=str(p),line=line))
r=dict(external_checks=checks,external_ok=all(x['ok'] for x in checks),id_range=[61000,61099],id_collisions=collisions,env=e,old_private_cache_exists=(D/'lean-objects').exists(),reuse_claim=False)
(D/'rdb2d-preflight.json').write_text(json.dumps(r,indent=2));print(json.dumps({k:v for k,v in r.items() if k not in ['external_checks','env']}),flush=True)
assert r['external_ok'] and not collisions
(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
