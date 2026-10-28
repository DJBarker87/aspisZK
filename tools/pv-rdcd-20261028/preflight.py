from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028')
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
roots=[Path(x) for x in e['LEAN_PATH'].split(':')];out=[];bad=[]
for r in json.load(open(D/'external-object-manifest.json')):
 if r['module'].split('/')[0] not in ['Init','Lean','Std']:continue
 p=next((p/(r['module']+'.olean') for p in roots if (p/(r['module']+'.olean')).exists()),None)
 h=hashlib.sha256(p.read_bytes()).hexdigest() if p else None
 x=dict(module=r['module'],path=str(p),expected=r['object_sha256'],actual=h)
 out.append(x)
 if h!=r['object_sha256']:bad.append(x)
(D/'preflight-results.json').write_text(json.dumps(dict(checked=out,bad=bad),indent=2)+'\n')
print('External preflight',len(out),'objects;',len(bad),'mismatches')
assert not bad,bad
(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
e['LEAN_PATH']=str(D/'lean-objects')+':'+e['LEAN_PATH']
(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
