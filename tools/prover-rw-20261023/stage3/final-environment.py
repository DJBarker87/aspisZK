"""Pin the final focused closure without compiling it again."""
from pathlib import Path
import hashlib,json
H=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023');E=H/'stage3'
J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
sha=lambda p:hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
root=json.loads((E/'11261-receipt.json').read_text());rows=[]
for d in root['dependencies']:
 p=Path(d['resolved_object']);digest=sha(p)
 assert digest==d['object_sha256'],('dependency changed since final audit',d['module'])
 rows.append(dict(module=d['module'],path=str(p),sha256=digest,bytes=p.stat().st_size))
last={}
for p in sorted(E.glob('*-receipt.json')):
 x=json.loads(p.read_text())
 if x['exit_status']==0:last[x['module']]=x
objects=[]
for m,r in last.items():
 src=J/'sources'/(m+'.lean');obj=J/'objects'/(m+'.olean')
 assert sha(src)==r['source_sha256'],('final source mismatch',m)
 objects.append(dict(module=m,last_compile=r['attempt'],source_sha256=sha(src),object_sha256=sha(obj),object_bytes=obj.stat().st_size))
envp=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
x=dict(root_attempt=11261,root_source_revision='d735d8174e6cdcc22eff9803ac4ac5cb6687f7b5',environment=json.loads(envp.read_text()),environment_sha256=sha(envp),all_final_audit_dependency_objects_unchanged=True,dependencies=rows,branch_modules=objects,qualification='Object pins for the final focused audit; not a coherent frozen release replay. Old overwritten objects are retained in branch-named snapshots, not committed.')
(E/'final-environment.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(unchanged_dependencies=len(rows),branch_modules=len(objects))))
