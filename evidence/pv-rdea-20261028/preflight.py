from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdea-20261028')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());roots=list(map(Path,e['LEAN_PATH'].split(':')))
m=json.loads(Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028/external-object-manifest.json').read_text()); checks=[]
for x in m:
 p=next((r/(x['module']+'.olean') for r in roots if (r/(x['module']+'.olean')).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 checks.append(dict(module=x['module'],path=str(p),expected=x['object_sha256'],actual=h,ok=h==x['object_sha256']))
for k,v in json.loads((D/'project-pins.json').read_text()).items():
 rel=k.replace('.','/');p=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).exists()),None)
 src=Path('/home/dombarker/project-offloads/aspis-joint-20261019/sources')/(rel+'.lean')
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 sh=hashlib.sha256(src.read_bytes()).hexdigest()
 checks.append(dict(module=k,path=str(p),expected=v['object_sha256'],actual=h,source_expected=v['source_sha256'],source_actual=sh,blob=v['blob'],ok=h==v['object_sha256'] and sh==v['source_sha256']))
j=dict(ok=all(c['ok'] for c in checks),checks=checks,env=e,errors=[c for c in checks if not c['ok']])
(D/'preflight.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(ok=j['ok'],checked=len(checks),errors=j['errors'])));assert j['ok']
