"""Read-only environment/object pinning after the focused audit; no replay."""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023');E=H/'stage3'
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
p=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads(p.read_text());paths=[J/'objects',*[Path(x) for x in env['LEAN_PATH'].split(':')]]
rows=[]
for q in sorted(E.glob('*-receipt.json')):
 r=json.loads(q.read_text());deps=[]
 for d in r['dependencies']:
  found=next((base/(d['module'].replace('.','/')+'.olean') for base in paths if (base/(d['module'].replace('.','/')+'.olean')).is_file()),None)
  assert found,(q,d)
  digest=sha(found)
  if d['object_sha256'] is not None:assert d['object_sha256']==digest,(q,d,found)
  deps.append(dict(**d,resolved_object=str(found),resolved_object_sha256=digest,base_import_pin_added_after_attempt=d['object_sha256'] is None))
 rows.append(dict(attempt=r['attempt'],dependencies=deps))
objects={}
for q in sorted(E.glob('*-receipt.json')):
 r=json.loads(q.read_text())
 if r['exit_status']==0:
  obj=J/'objects'/(r['module']+'.olean')
  if obj.is_file():objects[r['module']]=dict(path=str(obj),sha256=sha(obj),bytes=obj.stat().st_size)
x=dict(env=env,env_json_sha256=sha(p),private_launcher_sha256=sha(H/'src/tools/prover-rw-20261023/stage3/run-joint.sh'),existing_launcher_sha256=sha(p.parent.parent/'tools/run-joint.sh'),runner_sha256=sha(Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py')),all_recorded_dependency_objects_still_match=True,dependency_resolution=rows,final_focused_objects=objects,qualification='Post-run object/environment pins, not a coherent full frozen-release replay; compiled objects are hashed, never committed')
(E/'environment-audit.json').write_text(json.dumps(x,indent=2)+'\n')
