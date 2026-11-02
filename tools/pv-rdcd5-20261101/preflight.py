"""Capped external-authority verification, plain-copy overlay and h6 cache reuse."""
from pathlib import Path
import json,hashlib,shutil,re
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd5-20261101');old=Path('/home/dombarker/project-offloads/codex-pv-dlib-20261028')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
e=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'))
manifest=json.load(open(D/'external-object-manifest.json'));checked=[]
assert len(manifest)==5673
for r in manifest:
 p=Path(r['path']);assert sha(p)==r['object_sha256'],r['module']
 q=D/'external-objects'/(r['module']+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 for a in [p,*[p.with_suffix(s) for s in ['.ir','.olean.server','.olean.private']]]:
  if a.exists():
   b=q.parent/(q.stem+a.name[len(p.stem):]);shutil.copy2(a,b);assert sha(a)==sha(b)
 checked.append(dict(module=r['module'],path=str(q),sha256=sha(q)))
prior=json.load(open(old/'env-J.json'))
for k in ['LEAN','LEAN_GITHASH','ELAN_TOOLCHAIN']:assert e[k]==prior[k],k
# Both use the same shared suffix after job-private overlays.
assert e['LEAN_PATH'].split(':')==prior['LEAN_PATH'].split(':')[2:]
e['LEAN_PATH']=str(D/'lean-objects')+':'+str(D/'external-objects')+':'+e['LEAN_PATH']
(D/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True)
(D/'env-J.json').write_text(json.dumps(e,indent=2)+'\n')
plan=json.load(open(D/'source-resolution.json'));records=json.load(open(D/'h6-records.json'));reused={};rejected={}
roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
def effective(m):
 top=m.split('/')[0]
 root=next((r for r in roots if (r/top).is_dir()),None)
 return root/(m+'.olean') if root else None
for dotted in plan['compile_order']:
 m=dotted.replace('.','/');pin=plan['modules'][dotted];v=records.get(m,{})
 rec=v.get('recorded');o=v.get('object_record');s=v.get('source_record')
 if not rec or not o or not s:rejected[m]='missing original source/object/import receipt';continue
 p=Path(o['object_path'])
 if rec['source_sha256']!=pin['sha256'] or o['source_sha256']!=pin['sha256'] or s['source_sha256']!=pin['sha256']:
  rejected[m]='source version differs';continue
 if not p.exists() or sha(p)!=o['object_sha256']:rejected[m]='object missing or changed';continue
 mismatches=[]
 for dep,x in rec['imports'].items():
  dep=dep.replace('.','/');obj=effective(dep)
  if not obj or not obj.exists() or sha(obj)!=x['sha256'] or (dep.startswith('R1Z/') and dep not in reused):mismatches.append(dep)
 if mismatches:rejected[m]=dict(import_mismatches=mismatches);continue
 q=D/'lean-objects'/(m+'.olean');q.parent.mkdir(parents=True,exist_ok=True);companions={}
 for a in p.parent.glob(p.stem+'.*'):
  if a.is_file():
   b=q.parent/a.name;shutil.copy2(a,b);assert sha(a)==sha(b);companions[a.name]=sha(b)
 reused[m]=dict(source_sha256=pin['sha256'],object_sha256=sha(q),path=str(q),original_object=str(p),original_record=v,companions=companions)
resolution={}
for x in checked:
 p=effective(x['module']);assert p and p.exists() and sha(p)==x['sha256'];resolution[x['module']]=str(p)
for m,x in reused.items():
 p=effective(m);assert p and sha(p)==x['object_sha256'];resolution[m]=str(p)
# Missing project objects explicitly resolve into our complete-by-construction
# R1Z namespace, never into an unrelated shared source/object root.
for dotted in plan['compile_order']:
 m=dotted.replace('.','/');assert effective(m)==D/'lean-objects'/(m+'.olean')
(D/'preflight-result.json').write_text(json.dumps(dict(external_count=len(checked),external_manifest_sha256=sha(D/'external-object-manifest.json'),external=checked,reused=reused,rejected=rejected,effective_resolution=resolution,environment=e,prior_environment=prior,shared_prefix='identical shared suffix; own complete plain-copy overlays'),indent=2)+'\n')
print('Verified',len(checked),'external objects; reused',len(reused),'project objects;',len(rejected),'fresh builds required')
