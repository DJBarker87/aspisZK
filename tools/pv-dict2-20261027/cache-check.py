from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-dict2-20261027');B=D.parent;J=B/'aspis-joint-20261019';plan=json.loads((D/'closure-plan.json').read_text());env=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text());roots=[J/'objects',*[Path(p) for p in env['LEAN_PATH'].split(':')]]
rows={}
for m,x in plan['modules'].items():
 rel=m.replace('.','/');src=J/'sources'/(rel+'.lean');obj=next((r/(rel+'.olean') for r in roots if (r/(rel+'.olean')).exists()),None)
 sh=hashlib.sha256(src.read_bytes()).hexdigest() if src.exists() else None
 rows[m]=dict(source_sha256=sh,object=str(obj) if obj else None,object_sha256=hashlib.sha256(obj.read_bytes()).hexdigest() if obj else None,same_source=sh==x['source_sha256'])
(D/'cache-check.json').write_text(json.dumps(rows,indent=2)+'\n')
missing=[m for m,r in rows.items() if not r['object']];changed=[m for m,r in rows.items() if not r['same_source']];print('missing',len(missing),missing);print('different',len(changed),changed)
