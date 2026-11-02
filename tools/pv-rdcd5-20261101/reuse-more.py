"""Focused h6 extension in the already selected pv-dlib cohort; no compilation."""
from pathlib import Path
import hashlib,json,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-rdcd5-20261101')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
e=json.load(open(D/'env-J.json'));roots=[Path(x) for x in e['LEAN_PATH'].split(':')]
def obj(m):
 root=next((r for r in roots if (r/m.split('/')[0]).is_dir()),None)
 return root/(m+'.olean') if root else None
result=json.load(open(D/'preflight-result.json'));pins=json.load(open(D/'more-cache-records.json'));plan=json.load(open(D/'source-resolution.json'));added={};rejected={}
external=json.load(open(D/'external-object-manifest.json'))
for x in external:assert sha(obj(x['module']))==x['object_sha256']
for dotted in plan['compile_order']:
 m=dotted.replace('.','/');p=obj(m)
 if p and p.exists():continue
 v=pins.get(m)
 if not v:continue
 rec,o,s=v['recorded'],v['object_record'],v['source_record'];a=plan['modules'][dotted]
 if not (a['sha256']==o['source_sha256']==s['source_sha256']==rec['source_sha256']):rejected[m]='source mismatch';continue
 original=Path(o['object_path'])
 if not original.exists() or sha(original)!=o['object_sha256']:rejected[m]='object missing or changed';continue
 errors=[]
 for dep,x in rec['imports'].items():
  dep=dep.replace('.','/');q=obj(dep)
  if not q or not q.exists() or sha(q)!=x['sha256']:errors.append(dep)
 if errors:rejected[m]=errors;continue
 assert sha(D/'lean-sources'/(m+'.lean'))==a['sha256']
 for q in original.parent.glob(original.stem+'.*'):
  if q.is_file():
   dest=p.parent/q.name;shutil.copy2(q,dest);assert sha(q)==sha(dest)
 added[m]=dict(source_sha256=a['sha256'],object_sha256=sha(p),path=str(p),original_object=str(original),original_record=v)
 result['reused'][m]=added[m];result['rejected'].pop(m,None);result['effective_resolution'][m]=str(p)
(D/'preflight-result.json').write_text(json.dumps(result,indent=2)+'\n')
(D/'more-cache-result.json').write_text(json.dumps(dict(added=added,rejected=rejected,external_count=len(external),source='same pv-dlib cohort and original successful per-launch fingerprints'),indent=2)+'\n')
print('Additional h6 reused',len(added),'objects;',len(rejected),'rejected')
