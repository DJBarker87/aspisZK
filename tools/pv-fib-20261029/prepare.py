"""Read-only source/cohort verification, followed by staging own committed source."""
from pathlib import Path
import json, hashlib, subprocess, shlex
E=Path('evidence/pv-fib-20261029'); O=Path('evidence/pv-rj4idb-20261029')
H='/home/dombarker/project-offloads/codex-pv-fib-20261029'
rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
sha=lambda b:hashlib.sha256(b).hexdigest()
base=json.load(open(O/'source-resolution.json'))['projects']
checks={v['module']:v for v in json.load(open(O/'h6-result.json'))['result']['checks']}
records={}
for f in sorted(O.glob('modules-*.json')):
 for v in json.load(open(f)):
  if v['accepted']: records[v['module']]=v
plan=json.load(open(O/'build-plan.json'))['modules']
projects={}; edges=[]
for m,v in base.items():
 p=v['path']; selected=v['revision'] if 'runjoin' in v['authority'] else rev
 b=subprocess.check_output(['git','show',selected+':'+p])
 assert sha(b)==v['source_sha256'],('authority changed',m)
 projects[m]=dict(v,object_path=checks[m]['object_path'])
for m,v in records.items():
 p=plan[m]['path']; b=subprocess.check_output(['git','show',rev+':'+p])
 assert sha(b)==v['source_sha256'],('source changed',m)
 projects[m]=dict(module=m,path=p,revision=rev,source_sha256=sha(b),object_sha256=v['object_sha256'],object_path=H.replace('pv-fib','pv-rj4idb')+'/objects/'+m.replace('.','/')+'.olean')
 for d,r in v['dependencies'].items():edges.append(dict(module=m,dependency=d,sha256=r['sha256']))
# h6 project edges for the inherited project cohort
raw=subprocess.check_output(['git','show',rev+':evidence/pv-rj4id-20261029/inherited-reuse.json.xz'])
import lzma
reuse=json.loads(lzma.decompress(raw))
own=json.loads(subprocess.check_output(['git','show',rev+':evidence/pv-rj4id-20261029/inherited-validation.json']))
extra=json.loads(subprocess.check_output(['git','show',rev+':evidence/pv-rj4id-20261029/extra-records.json']))
edges+=reuse['dependencies']+own['dependencies']
edges += [dict(module=m,dependency=d,sha256=v['sha256']) for m,r in extra['records'].items() for d,v in r['dependencies'].items()]
external=json.loads(subprocess.check_output(['git','show',rev+':evidence/pv-rj4id-20261029/external-authority.json']))
# Only load the recorded import closure, not every object in a cache.
new=Path('lean/PV_FIB_Restricted.lean');b=new.read_bytes()
assert subprocess.check_output(['git','show',rev+':'+str(new)])==b
payload=dict(H=H,revision=rev,projects=projects,edges=edges,external=external,source=b.decode(),sha256=sha(b))
code=r'''
import pathlib,json,sys,hashlib,subprocess,re
x=json.load(sys.stdin);p=pathlib.Path(x['H']);old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rj4idb-20261029')
env=json.load(open(old/'J.json')); roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')]
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ext=x['external'];print_type=type(ext).__name__
if isinstance(ext,dict): ext=ext.get('objects',ext.get('modules',ext.get('entries',ext)))
assert isinstance(ext,list),('manifest shape',print_type,list(ext)[:8])
auth={v['module'].replace('/','.'):v for v in ext}
visited={};used=[]
def resolve(m):
 return next(q/(m.replace('.','/')+'.olean') for q in roots if (q/(m.replace('.','/')+'.olean')).is_file())
def visit(m):
 if m in visited:return
 q=resolve(m);digest=sha(q)
 if m in x['projects']:
  v=x['projects'][m];assert digest==v['object_sha256'],('object changed',m)
  visited[m]=dict(module=m,path=str(q),sha256=digest,source=v)
  es=[e for e in x['edges'] if e['module']==m]
  for e in es:
   d=e['dependency'];assert sha(resolve(d))==e.get('expected',e.get('sha256')),('cohort edge',m,d)
   visit(d)
 else:
  v=auth[m];assert digest==v['object_sha256'],('external changed',m)
  visited[m]=dict(module=m,path=str(q),sha256=digest,authority='coherent privacy external manifest')
# External manifest audited in full, including transitive implicit Init imports.
for m,v in auth.items():
 q=resolve(m);assert sha(q)==v['object_sha256'],('external',m)
 used.append(dict(module=m,path=str(q),sha256=v['object_sha256']))
for m in ['R1Z.ProverCommitFuelJoin22','PV_RJ4IDB_SourceTrace']:visit(m)
for n in ['sources','objects','evidence']:(p/n).mkdir(parents=True,exist_ok=True)
(p/'sources/PV_FIB_Restricted.lean').write_text(x['source'])
env['LEAN_PATH']=str(p/'objects')+':'+env['LEAN_PATH'];(p/'J.json').write_text(json.dumps(env))
print(json.dumps(dict(project_checks=list(visited.values()),external_checks=used,toolchain=env['LEAN_GITHASH'],inherited_prefix=':'.join(str(q) for q in roots),LEAN_PATH=env['LEAN_PATH'],source_revision=x['revision'],source_sha256=x['sha256'],shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
(E/'prepare-result.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2)+'\n')
assert r.returncode==0,r.stderr+r.stdout
print('PASS verified and staged')
