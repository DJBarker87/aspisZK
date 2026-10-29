"""Coherent own project DAG plus h4 objects; no compilation or other-job writes."""
from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028')
pins=json.load(open(D/'v260-source-resolution.json'));env=json.load(open(D/'env-J.json'));roots=[Path(p) for p in env['LEAN_PATH'].split(':')]
external={r['module']:r for r in json.load(open(D/'external-object-manifest.json'))}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def obj(m):return next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None)
for m,j in external.items():
 p=obj(m);assert p and sha(p)==j['object_sha256'],m
seen={}
for module,j in pins['modules'].items():
 m=module.replace('.','/');s=D/'lean-sources'/(m+'.lean');p=obj(m)
 assert s.exists() and sha(s)==j['sha256'],module
 assert p==D/'lean-objects'/(m+'.olean'),(module,p)
 imports={}
 for dep in j['imports']:
  d=dep.replace('.','/');q=obj(d);assert q,(module,dep)
  assert dep in pins['modules'] or d in external,(module,dep,'no authority')
  imports[dep]=dict(path=str(q),sha256=sha(q))
 seen[module]=dict(**j,object_path=str(p),object_sha256=sha(p),imports_actual=imports)
result=dict(source_revision=pins['revision'],project_modules=seen,external_count=len(external),external_manifest_sha256=sha(D/'external-object-manifest.json'),environment=env,authority=pins['higher_priority_absence'],measurement='Current coherent DAG after focused V260 proofs; individual at-submission dependency snapshots remain in each receipt')
(D/'v260-fingerprint-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(len(seen),'private source/object/import bindings and',len(external),'external object hashes coherent')
