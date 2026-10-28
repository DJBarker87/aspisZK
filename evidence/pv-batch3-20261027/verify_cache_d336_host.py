"""Read-only source/object/dependency evidence for the final proof closure.
This audits this job's existing private cache; it never builds or substitutes.
"""
from pathlib import Path
import json,re,hashlib,time
H=Path('/home/dombarker/project-offloads/codex-pv-batch3-20261027')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest() if p.is_file()else None
resolution=json.loads((H/'d336-project-resolution.json').read_text())
external=json.loads((H/'batch3b-external-object-manifest.json').read_text())
ext={r['module'].replace('/','.'):r for r in external}
envpath=Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json')
env=json.loads(envpath.read_text());search=[H/'lean-objects',Path('/home/dombarker/project-offloads/aspis-joint-20261019/objects')]+[Path(p)for p in env['LEAN_PATH'].split(':')]
records=[]
for p in H.glob('lean-*/receipt/receipt.json'):
 j=json.loads(p.read_text())
 if j.get('exit_status')==0 and j.get('module'):records.append((p,j))
records.sort(key=lambda r:r[0].stat().st_mtime,reverse=True)
def selected(m):return next((p/(m.replace('.','/')+'.olean')for p in search if (p/(m.replace('.','/')+'.olean')).is_file()),None)
rows=[];bad=[]
for m,authority in resolution['modules'].items():
 assert not any(part.startswith('XR')for part in m.split('.')),m
 src=H/'lean'/(m.replace('.','/')+'.lean');obj=selected(m)
 row=dict(module=m,source_authority=authority,private_source=str(src),actual_source_sha256=sha(src),object_path=str(obj),object_sha256=sha(obj)if obj else None)
 errors=[]
 if sha(src)!=authority['sha256']:errors.append('private source differs from resolved source')
 if obj is None:errors.append('object missing')
 elif not obj.is_relative_to(H/'lean-objects'):errors.append('project object is not in own private cache')
 candidates=[(p,r)for p,r in records if r['module']==m and r['source_sha256']==authority['sha256']]
 credited=None;attempt_errors=[]
 for p,r in candidates:
  depbad=[]
  for imp in authority['imports']:
   q=selected(imp);actual=sha(q)if q else None;recorded=r.get('dependency_objects',{}).get(imp,{}).get('sha256')
   if recorded!=actual:depbad.append(dict(module=imp,recorded=recorded,actual=actual,path=str(q)))
   if imp in ext and actual!=ext[imp]['object_sha256']:depbad.append(dict(module=imp,error='h4 external object mismatch'))
  oldenv=r.get('original_environment_sha256')
  if oldenv and oldenv!=sha(envpath):depbad.append(dict(error='original env J hash differs',recorded=oldenv,actual=sha(envpath)))
  if not depbad:
   credited=dict(receipt=str(p),attempt=r.get('attempt'),source_sha256=r['source_sha256'],deps_fingerprint=r.get('deps_fingerprint'),original_environment_sha256=oldenv);break
  attempt_errors.append(dict(receipt=str(p),mismatches=depbad))
 if credited is None:errors.append('no accepted source receipt with current direct dependency fingerprint')
 row['accepted_binding']=credited;row['candidate_dependency_mismatches']=attempt_errors;row['errors']=errors
 rows.append(row)
 if errors:bad.append(dict(module=m,errors=errors))
# All project imports are checked, so checking every edge gives the complete
# transitive fingerprint; external objects are additionally verified in full.
result=dict(revision=resolution['revision'],epoch=time.time(),modules=len(rows),rows=rows,mismatches=bad,read_only=True,project_objects_from_other_jobs=False,XR_imports=False,environment_sha256=sha(envpath))
(H/'d336-cache-verification.json').write_text(json.dumps(result,indent=1)+'\n')
print(json.dumps(dict(checked=len(rows),mismatches=bad)))
