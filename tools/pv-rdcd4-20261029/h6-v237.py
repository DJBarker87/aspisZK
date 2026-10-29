"""Expected phase: source/object/import hashing and copying verified cache files.
No compilation, arithmetic, elimination, or previous checker replay occurs here.
"""
from pathlib import Path
import json,hashlib,re,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd3-20261028/rdcd4-20261029')
old=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028')
inputs=json.load(open(D/'v237-h6-inputs.json'));meta=inputs['authority_resolution'];records=inputs['records']
env=json.load(open(D/'env-J.json'));prior=json.load(open(old/'env-J.json'))
roots=[Path(x) for x in env['LEAN_PATH'].split(':')]
assert prior['LEAN_PATH'].split(':')[2:]==env['LEAN_PATH'].split(':')[2:]
for key in ['LEAN','LEAN_GITHASH','ELAN_TOOLCHAIN']:assert prior[key]==env[key],key

def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def obj(module):return next((r/(module+'.olean') for r in roots if (r/(module+'.olean')).exists()),None)
# Check the external cohort before considering any object from the old cache.
external=json.load(open(D/'external-object-manifest.json'))
for pin in external:
 p=obj(pin['module']);assert p and sha(p)==pin['object_sha256'],pin['module']
reused={};rejected={};existing={}
for dotted in meta['compile_order']:
 module=dotted.replace('.','/');pin=records[module];authority=pin['authority'];rec=pin['recorded'];o=pin['object_record'];s=pin['source_record']
 current=obj(module)
 if current and current.resolve()==(D/'lean-objects'/(module+'.olean')).resolve():
  existing[module]=dict(path=str(current),sha256=sha(current));continue
 if not rec or not o or not s:
  rejected[module]=['missing original successful source/object/import receipt'];continue
 assert rec['source_sha256']==authority['sha256']==o['source_sha256']==s['source_sha256'],module
 source=D/'h6-staged-sources'/(module+'.lean');assert sha(source)==authority['sha256'],module
 original=Path(o['object_path']);assert sha(original)==o['object_sha256'],module
 imports=re.findall(r'^import\s+(\S+)',source.read_text(),re.M)
 assert set(x.replace('.','/') for x in imports)==set(s['imports']),module
 mismatches=[];checked={}
 for dep,value in rec['imports'].items():
  name=dep.replace('.','/');p=obj(name)
  if not p or sha(p)!=value['sha256']:
   mismatches.append(dict(module=name,recorded=value['sha256'],current=sha(p) if p else None))
  else:checked[name]=dict(path=str(p),object_sha256=sha(p))
 if mismatches:rejected[module]=mismatches;continue
 # Every project dependency must itself have a checked old source record or
 # be one of this job's original successful private modules.
 for dep in checked:
  if dep.startswith('R1Z/') and dep not in reused and dep not in existing:
   raise AssertionError(('incomplete project fingerprint',module,dep))
 dest=D/'lean-objects'/(module+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
 assert not dest.exists(),module
 companions={}
 for p in original.parent.glob(original.stem+'.*'):
  if p.is_file():
   q=dest.parent/p.name;assert not q.exists(),str(q);shutil.copy2(p,q);assert sha(q)==sha(p)
   companions[p.name]=dict(original=str(p),sha256=sha(p))
 target=D/'lean-sources'/(module+'.lean');target.parent.mkdir(parents=True,exist_ok=True);assert not target.exists();shutil.copy2(source,target)
 reused[module]=dict(reused=True,attempt=None,old_attempt=rec['attempt'],source_path=authority['path'],source_sha256=authority['sha256'],source_blob=authority['blob'],source_revision=meta['revision'],object_path=str(dest),object_sha256=o['object_sha256'],original_object_path=str(original),original_receipt=rec,imports=checked,companions=companions,authority='h5 tracked HEAD with mechanical EJR/freeze absence census; h6 exact recorded source/object and complete loaded dependency cohort',reuse_native_scope='h6-v237')
# Record every rejection; missing/cohort-mismatching objects must be built fresh.
out=dict(modules=reused,rejected=rejected,existing=existing,external_count=len(external),environment=env,old_environment=prior,shared_LEAN_PATH_prefix='identical after the two private object/authority overlays',old_fingerprint_sha256=inputs['old_fingerprint_sha256'],scope='h6 verified read-only old cache; copies only in own directory; no old project object with a changed import fingerprint was accepted')
(D/'reused-projects.json').write_text(json.dumps(out,indent=2)+'\n');print('h6 verified',len(reused),'reusable objects;',len(rejected),'require fresh build;',len(existing),'already private.')
