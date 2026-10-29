from pathlib import Path
import json,hashlib,subprocess
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');M=json.loads((H/'input-external-object-manifest.json').read_text());cohorts=json.loads((H/'cohorts.json').read_text());out=[]
for cohort,path in cohorts.items():
 roots=[Path(x)for x in path.split(':')]
 for x in M:
  mod=x['module'];top=mod.split('/')[0]
  root=next((r for r in roots if(r/top).exists() or(r/(top+'.olean')).exists()),None)
  p=root/(mod+'.olean') if root else None
  h=hashlib.sha256(p.read_bytes()).hexdigest() if p and p.exists() else None
  out.append(dict(cohort=cohort,module=mod,path=str(p),sha256=h,authority_sha256=x['object_sha256'],matches_authority=h==x['object_sha256']))
(H/'resolution.json').write_text(json.dumps(out,indent=1))
print(json.dumps({k:{'total':len([x for x in out if x['cohort']==k]),'missing':len([x for x in out if x['cohort']==k and x['sha256'] is None]),'differences':len([x for x in out if x['cohort']==k and not x['matches_authority']]),'fmt':[x for x in out if x['cohort']==k and x['module']=='Aeneas/Std/Core/Fmt']} for k in cohorts},indent=2))
