"""Expected phase: hash final source/object/import cohort and reused source gates.
No arithmetic, compilation or unchanged regression suite runs here.
"""
from pathlib import Path
from functools import lru_cache
import json,hashlib,re,subprocess
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
@lru_cache(None)
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
env=json.load(open(D/'env-J.json'));roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
external={x['module']:x for x in json.load(open(D/'external-object-manifest.json'))}
meta=json.load(open(D/'final-coherence-inputs.json'));modules=meta['modules']
def obj(m):return next((r/(m+'.olean') for r in roots if (r/(m+'.olean')).exists()),None)
for module,pin in external.items():
 p=obj(module);assert p and sha(str(p))==pin['object_sha256'],('external mismatch',module)
records={};snapshots={}
for module,pin in modules.items():
 source=D/'lean-sources'/(module+'.lean');p=obj(module)
 assert sha(str(source))==pin['source_sha256'],('source mismatch',module)
 assert p.resolve()==(D/'lean-objects'/(module+'.olean')).resolve(),('private project object required',module,p)
 imports={}
 for dep in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
  m=dep.replace('.','/');q=obj(m);assert q,(module,m)
  assert m in modules or m in external,('unresolved import authority',module,m)
  imports[m]=dict(path=str(q),sha256=sha(str(q)))
 snapshot=json.load(open(D/'final-launch-snapshots'/(str(pin['attempt'])+'.json')))
 assert snapshot['environment']==env,('environment changed',module)
 for dep,old in snapshot['objects'].items():
  q=obj(dep);assert q and sha(str(q))==old['object_sha256'],('launch/final import object mismatch',module,dep)
  if 'source_sha256' in old:
   assert dep in modules and old['source_sha256']==modules[dep]['source_sha256'],('launch/final import source mismatch',module,dep)
 snapshots[module]=dict(attempt=pin['attempt'],objects_checked=len(snapshot['objects']))
 records[module]=dict(**pin,object_path=str(p),object_sha256=sha(str(p)),imports=imports)
library=json.load(open(D/'library-sources.json'))
for record in library:
 assert sha(record['path'])==record['sha256'],('deployed Rust library source changed',record['path'])
for pin in meta.get('additional_native_source_pins',[]):
 assert sha(pin['path'])==pin['sha256'],('additional deployed source changed',pin['path'])
out=dict(additional_native_source_pins=meta.get('additional_native_source_pins',[]),source_revision=meta['revision'],modules=records,at_launch_snapshots=snapshots,external_count=len(external),external_manifest_sha256=sha(str(D/'external-object-manifest.json')),environment=env,scope='Final independent coherent source/object/import measurement, with comparison to each actual launch snapshot. No retroactive launch measurement is claimed.',deployed_library_files=len(library),compiler_boundary='V370/D381/D386 and existing Aeneas/Rust semantic trust retained; no endpoint premise removal')
(D/'final-coherence-result.json').write_text(json.dumps(out,indent=2)+'\n');print(len(records),'successful private modules and all',len(external),'external hashes coherent with every launch snapshot')
