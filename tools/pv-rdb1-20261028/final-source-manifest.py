from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb1-20261028')
checks=[];inputs=[]
def visit(x):
 if isinstance(x,dict):
  if x.get('file_sha256') and x.get('file'):
   p=Path(x['file']);actual=hashlib.sha256(p.read_bytes()).hexdigest()
   checks.append(dict(path=str(p),expected=x['file_sha256'],actual=actual,ok=actual==x['file_sha256']))
  for v in x.values():visit(v)
 elif isinstance(x,list):
  for v in x:visit(v)
for row in ['V164','V170','V178','V181','V182','V183','V184','V186','V187','V195','V198','V219']:
 p=D/('v186-structural.json' if row=='V186' else row.lower()+'-deployed-binding.json')
 b=p.read_bytes();inputs.append(dict(row=row,path=str(p),sha256=hashlib.sha256(b).hexdigest()));visit(json.loads(b))
assert checks and all(x['ok'] for x in checks)
j=dict(ok=True,scope='Final source identity of complete deployed-body bindings, including stopped finding rows; no new behaviour proof or repeated native fixture',inputs=inputs,checks=checks,features=dict(path='resolved-features.json',sha256=hashlib.sha256((D/'resolved-features.json').read_bytes()).hexdigest()),toolchain='1.94.1',profile='release opt3; debug_assertions=false; overflow_checks=false; panic=unwind')
(D/'final-source-manifest.json').write_text(json.dumps(j,indent=2)+'\n');print('PASS final source identity',len(checks),'body-file checks',len(inputs),'rows')
