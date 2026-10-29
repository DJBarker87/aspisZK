"""Verify inherited h6 source/object cohort, reuse read-only, stage own source."""
import json,hashlib,subprocess,shlex,sys
from pathlib import Path
E=Path('evidence/pv-l2e-20261029');H='/home/dombarker/project-offloads/codex-pv-l2e-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
m=sys.argv[1];assert m.startswith('PV_L2E_')
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
s=Path('lean')/(m+'.lean');b=s.read_bytes();assert subprocess.check_output(['git','show',rev+':'+str(s)])==b
base=json.load(open('evidence/pv-fib-20261029/prepare-PV_FIB_Restricted.json'))['result']
projects=[v for v in base['project_checks'] if 'source' in v]
for v in projects:
 a=v['source'];p=a['path'];r=a['revision'] if 'EJR' in a['authority'] or 'freeze' in a['authority'] or 'runjoin' in a['authority'] else rev
 raw=subprocess.check_output(['git','show',r+':'+p]);assert sha(raw)==a['source_sha256'],('source changed',v['module'])
r=json.load(open('evidence/pv-fib-20261029/receipt-67504.json'))
projects.append(dict(module='PV_FIB_Restricted',path='/home/dombarker/project-offloads/codex-pv-fib-20261029/objects/PV_FIB_Restricted.olean',source=dict(source_sha256=r['source_sha256']),sha256=None))
assert sha(subprocess.check_output(['git','show',rev+':lean/PV_FIB_Restricted.lean']))==r['source_sha256']
code=r'''
import json,pathlib,sys,hashlib,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['H']);old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-fib-20261029')
env=json.load(open(old/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')]
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
def resolve(m):return next(q/(m.replace('.','/')+'.olean') for q in roots if (q/(m.replace('.','/')+'.olean')).is_file())
checks=[]
for v in x['base']['external_checks']+x['projects']:
 q=resolve(v['module']);expected=v.get('sha256')
 if expected is None:
  assert v['module']=='PV_FIB_Restricted'
  assert sha(old/'sources/PV_FIB_Restricted.lean')==v['source']['source_sha256']
  expected=sha(q)
 assert sha(q)==expected,('changed object',v['module'])
 checks.append(dict(module=v['module'],path=str(q),sha256=expected))
for d in ['objects','sources','evidence']:(p/d).mkdir(parents=True,exist_ok=True)
# Preserve the verified predecessor prefix. Do not modify its sources or objects.
env['LEAN_PATH']=str(p/'objects')+':'+env['LEAN_PATH'];(p/'J.json').write_text(json.dumps(env))
(p/('sources/'+x['module']+'.lean')).write_text(x['source'])
print(json.dumps(dict(checks=checks,toolchain=env['LEAN_GITHASH'],LEAN_PATH=env['LEAN_PATH'],source_revision=x['revision'],source_sha256=x['sha'],source=x['module'],inherited_prefix=':'.join(map(str,roots)))))
'''
payload=dict(H=H,module=m,source=b.decode(),sha=sha(b),revision=rev,projects=projects,base=base)
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
(E/('prepare-'+m+'.json')).write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2)+'\n')
assert r.returncode==0,r.stderr+r.stdout
print('PASS',m,'h6 objects and 5673 external objects; staged committed source')
