"""Verify accepted private project closure plus every h4 external object."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd-20261028');pins=json.load(open(D/'resume-final-source-pins.json'));env=json.load(open(D/'env-J.json'));roots=[Path(x) for x in env['LEAN_PATH'].split(':')];external={x['module']:x for x in json.load(open(D/'external-object-manifest.json'))};seen={}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(m):return next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None)
for m,j in external.items():
 p=obj(m);assert p is not None and sha(p)==j['object_sha256'],m
for m,j in pins['modules'].items():
 assert not m.split('/')[-1].startswith('XR'),m
 s=D/'lean-sources'/(m+'.lean');p=obj(m);assert sha(s)==j['sha256'],m
 assert p==D/'lean-objects'/(m+'.olean'),(m,p)
 imports={}
 for dep in j['imports']:
  q=obj(dep);assert q is not None,(m,dep)
  assert dep in pins['modules'] or dep in external,(m,dep,'unresolved authority')
  imports[dep]=dict(object_path=str(q),object_sha256=sha(q))
 seen[m]=dict(**j,object_path=str(p),object_sha256=sha(p),object_bytes=p.stat().st_size,resolved_imports=imports)
# The complete DAG is recorded; no child may resolve to another project's object.
(D/'resume-final-fingerprint.json').write_text(json.dumps(dict(source_revision=pins['source_revision'],modules=seen,authority_absence_checks=pins['authority_absence_checks'],external_count=len(external),external_manifest_sha256=sha(D/'external-object-manifest.json'),environment=env,other_job_project_objects_reused=False,roots=pins['roots']),indent=2)+'\n');print(len(seen),'private project source/object/import fingerprints verified;',len(external),'external pins verified')
