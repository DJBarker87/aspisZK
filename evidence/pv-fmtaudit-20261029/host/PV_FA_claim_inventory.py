from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029');co=json.loads((H/'cohorts.json').read_text());rows=json.loads((H/'credited-row-input.json').read_text());out=[]
for k,path in co.items():
 if k=='authority':continue
 roots=[Path(x)for x in path.split(':')]
 # b3q's own new modules are in its private namespace-complete directory.
 if k=='b3q':roots=[H.parent/'codex-pv-b3q-20261029/lean-objects']+roots
 for row in rows:
  t=row.get('closure_theorem')
  if not t:continue
  mod=t.rsplit('.',1)[0];top=mod.split('.')[0];r=next((r for r in roots if(r/top).exists()or(r/(top+'.olean')).exists()),None);p=r/(mod.replace('.','/')+'.olean')if r else None
  out.append(dict(cohort=k,id=row['id'],theorem=t,module=mod,path=str(p),exists=bool(p and p.exists()),sha256=hashlib.sha256(p.read_bytes()).hexdigest()if p and p.exists()else None))
(H/'claim-object-resolution.json').write_text(json.dumps(out,indent=1));print({k:[x['id']for x in out if x['cohort']==k and x['exists']]for k in co})
