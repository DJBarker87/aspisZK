from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-op254-20261027')
e=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
roots=[H/'lean-objects',Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects')]+[Path(x) for x in e['LEAN_PATH'].split(':')]
checks=[]
for x in json.loads((H/'external-object-manifest.json').read_text()):
 obj=next((r/(x['module']+'.olean') for r in roots if (r/(x['module']+'.olean')).exists()),None)
 actual=hashlib.file_digest(obj.open('rb'),'sha256').hexdigest() if obj else None
 checks.append(dict(module=x['module'],resolved=str(obj),match=actual==x['object_sha256'],sha256=actual,expected=x['object_sha256']))
(H/'external-effective-verification.json').write_text(json.dumps(checks,indent=2)+'\n')
bad=[x for x in checks if not x['match']];print(json.dumps(dict(checked=len(checks),mismatches=bad)))
assert not bad
