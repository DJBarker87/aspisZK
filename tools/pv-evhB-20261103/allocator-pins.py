"""Resolve only the three V183 additions from the pinned runjoin32 cohort."""
from pathlib import Path
import json,subprocess,hashlib,shlex
E=Path('evidence/pv-evhB-20261103');x=json.load(open(E/'allocator-extension.json'))
rev=x['authority_revision']
raw=subprocess.check_output(['git','show',rev+':'+x['preflight_path']]);pre=json.loads(raw)
base=json.load(open('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json'))['result']
ext={v['module']:v for v in base['external_checks']}
assert all(v['sha256']==ext[v['module']]['sha256']==v['expected'] for v in pre['external'])
x['external_manifest_sha256']=hashlib.sha256(raw).hexdigest()
for v in x['project_checks']:
 s=v['source'];b=subprocess.check_output(['git','show',s['revision']+':'+s['path']]);assert hashlib.sha256(b).hexdigest()==s['source_sha256']
needed=set(v['module'] for v in x['project_checks'])
x['dependency_checks']=[v for v in pre['dependencies'] if v['module'] in needed]
assert all(v['match'] and v['sha256']==v['expected'] for v in x['dependency_checks'])
code=r'''
import json,pathlib,hashlib,sys,shutil
x=json.load(sys.stdin);seen=[]
for v in x['project_checks']:
 p=pathlib.Path(v['original_object_path']);q=pathlib.Path(v['path'])
 assert hashlib.sha256(p.read_bytes()).hexdigest()==v['sha256']
 if q.exists(): assert hashlib.sha256(q.read_bytes()).hexdigest()==v['sha256']
 else:
  q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
 for suffix in ['.ilean','.olean.private','.olean.server','.ir']:
  a=p.with_suffix(suffix);b=q.with_suffix(suffix)
  if a.exists():
   if b.exists(): assert a.read_bytes()==b.read_bytes()
   else: shutil.copyfile(a,b)
 seen.append(dict(module=v['module'],path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
print(json.dumps(seen))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(x),text=True,capture_output=True)
(E/'allocator-copy.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');assert r.returncode==0,r.stderr
(E/'allocator-extension.json').write_text(json.dumps(x,indent=2)+'\n');print('PASS three same-cohort additions; all external hashes match')
