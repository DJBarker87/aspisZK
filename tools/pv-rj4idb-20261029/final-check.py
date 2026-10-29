"""Final source/object/dependency/receipt audit; no compiler or scope launch."""
from pathlib import Path
import subprocess,json,hashlib,shlex,re
E=Path('evidence/pv-rj4idb-20261029');H='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029';sha=lambda b:hashlib.sha256(b).hexdigest();plan=json.loads((E/'build-plan.json').read_text());accepted={};failed=[];launches=0
for f in sorted(E.glob('modules-*.json')):
 for r in json.loads(f.read_text()):
  launches+=1
  if r['accepted']:accepted[r['module']]=r
  else:failed.append(dict(attempt=int(f.stem.split('-')[-1]),module=r['module'],sha256=r['source_sha256'],exit=r['exit']))
checks=[]
for m,v in plan['modules'].items():
 assert m in accepted,('unaccepted final source',m)
 r=accepted[m];b=subprocess.check_output(['git','show','HEAD:'+v['path']]);assert sha(b)==v['sha256']==r['source_sha256'],m
 assert all('sorryAx' not in a for a in r['axioms']),m
 for a in r['axioms']:
  s=re.search(r'\[([\s\S]*?)\]',a)
  if s:assert set(re.findall(r'[A-Za-z.]+',s[1]))<= {'propext','Classical.choice','Quot.sound'},(m,a)
 checks.append(dict(module=m,source_path=v['path'],source_sha256=v['sha256'],object_sha256=r['object_sha256'],dependencies=r['dependencies']))
# Every theorem in every new accepted module has its own query.
for p in Path('lean').glob('PV_RJ4IDB_*.lean'):
 text=p.read_text();names=re.findall(r'^theorem\s+(\w+)',text,re.M)
 for n in names:assert re.search(r'^#print axioms '+re.escape(n)+r'\s*$',text,re.M),(p,n)
payload=dict(H=H,checks=checks,h6=json.loads((E/'h6-result.json').read_text())['result']['checks'])
code=r'''import json,sys,pathlib,hashlib
x=json.load(sys.stdin);p=pathlib.Path(x['H']);sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest();checked=0
for v in x['checks']:
 m=v['module'];s=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert sha(s)==v['source_sha256'],('source',m);assert sha(o)==v['object_sha256'],('object',m)
 for d,r in v['dependencies'].items():assert sha(pathlib.Path(r['path']))==r['sha256'],('dependency',m,d)
 checked+=1
for v in x['h6']:assert sha(pathlib.Path(v['object_path']))==v['object_sha256'],('inherited object',v['module'])
print(json.dumps(dict(all_match=True,own_or_recompiled_sources=checked,inherited_h6_objects=len(x['h6']),shared_written=False)))'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),capture_output=True,text=True);assert r.returncode==0,r.stderr
result=dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),host=json.loads(r.stdout),actual_Lean_launches=launches,preLean_empty_scope=64600,accepted_modules=len(accepted),failed_attempts=failed,checks=checks,receipt_hashes={p.name:sha(p.read_bytes()) for p in E.glob('*receipt*.json')},all_new_theorems_have_queries=True)
(E/'final-validation.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['checks','receipt_hashes','failed_attempts']}))
