"""Read-only validation of external object pins before the private Init-only proof."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-kstub-20261028')
manifest=Path('/home/dombarker/project-offloads/codex-pv-relink-20261028') # source/evidence only
# The committed coherent replay manifest is supplied with this job.
rows=json.loads((D/'external-object-manifest.json').read_text());out=[]
for x in rows:
 if not (x['module']=='Init' or x['module'].startswith('Init/') or x['module']=='Std' or x['module'].startswith('Std/')):continue
 p=Path(x['path']);h=hashlib.sha256(p.read_bytes()).hexdigest();out.append(dict(module=x['module'],path=str(p),sha256=h,expected=x['object_sha256'],ok=h==x['object_sha256']))
assert out and all(x['ok'] for x in out)
(D/'lean-external-preflight.json').write_text(json.dumps(out,indent=2))
# Isolated Lean path: no project object and no Stream A object.
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text());e['LEAN_PATH']=str(Path(e['LEAN']).parents[1]/'lib/lean');(D/'env-J.json').write_text(json.dumps(e,indent=2))
print(len(out),'Init/Std external objects verified')
