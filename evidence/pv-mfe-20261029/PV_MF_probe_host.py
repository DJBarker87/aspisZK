from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-mfe-20261029');J=json.load(open(D/'provenance-input.json'));sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();F=json.load(open(D.parent/'codex-pv-mfb-20261029/dlib-preflight-input.json'));roots=[Path(x) for x in F['environment']['LEAN_PATH'].split(':')]
def resolve(m):return next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).exists()),None)
res=[]
for key,v in J.items():
 j=v['content']
 if not isinstance(j,dict) or 'dependencies' not in j:continue
 ds=j['dependencies'];diff=[];ok=[]
 for x in ds:
  m=x['module'];p=resolve(m);expected=x.get('sha256',x.get('object_sha256'));actual=sha(p) if p else None
  z=dict(module=m,expected=expected,actual=actual,path=str(p));(ok if actual==expected else diff).append(z)
 res.append(dict(evidence=key,sha256=v['sha256'],matched=len(ok),mismatches=diff))
(D/'provenance-probe.json').write_text(json.dumps(res,indent=2)+'\n')
for r in res:print(r['evidence'],r['matched'],'matches',len(r['mismatches']),'mismatches',r['mismatches'][:3])
