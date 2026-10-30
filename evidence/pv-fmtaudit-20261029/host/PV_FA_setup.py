from pathlib import Path
import json,hashlib,subprocess,os
H=Path('/home/dombarker/project-offloads/codex-pv-fmtaudit-20261029'); B=H.parent/'codex-pv-b3q-20261029'
s=(B/'run.py').read_text().replace(str(B),str(H)).replace('pv-b3q-','pv-fmtaudit-')
(H/'run.py').write_text(s);(H/'capped.py').write_bytes((B/'capped.py').read_bytes())
env=json.loads((B/'env-J-private.json').read_text());
cohorts={'b3q':env['LEAN_PATH'],'event':json.loads((H.parent/'codex-pv-runjoin-20261026/runjoin32-lean/J.json').read_text())['LEAN_PATH'],'ndr':str(H.parent/'codex-cx-reconcile-cache-20261028/objects')+':'+env['LEAN_SYSROOT']+'/lib/lean'}
manifest=json.loads((H/'input-external-object-manifest.json').read_text()); roots=[]
for x in manifest:
 r=x['path'][:-len(x['module']+'.olean')].rstrip('/')
 if r not in roots:roots.append(r)
cohorts['authority']=':'.join(roots)
for k,path in cohorts.items():
 e=dict(env,LEAN_PATH=path);(H/(k+'.json')).write_text(json.dumps(e,indent=2))
(H/'cohorts.json').write_text(json.dumps(cohorts,indent=2))
