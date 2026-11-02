"""Source/cohort-verified extension to the existing recorded runjoin61 project cohort.
No build, LEAN_PATH edit, or library authority extension. Only hash-identical
plain copies replace own project-overlay symlinks under h6 namespace rules.
"""
from pathlib import Path
import hashlib,json,subprocess,shlex
E=Path('evidence/pv-evh8-20261101');sha=lambda b:hashlib.sha256(b).hexdigest()
rev=json.load(open('evidence/pv-evh2-20261029/binding-source-pins.json'))[0]['revision']
def read(p):return json.loads(subprocess.check_output(['git','show',rev+':'+p]))
plan=read('evidence/pv-runjoin61-20261029/build-plan.json');pre=read('evidence/pv-runjoin61-20261029/fresh-preflight.json')
objects={v['module']:v for v in pre['projects']};edges=pre['dependencies'];base=json.load(open('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json'))['result'];ext={v['module']:v for v in base['external_checks']};known={v['module']:v for v in base['project_checks']};checks={};usededges=[]
def visit(m):
 if m in checks or m in known or m in ext:return
 v=plan['modules'][m];o=objects[m];assert o['source_sha256']==v['sha256']==o['expected_source_sha256']
 selected=rev if v['authority'].startswith('h5') else v.get('revision',rev)
 raw=subprocess.check_output(['git','show',selected+':'+v['path']]);assert sha(raw)==v['sha256']
 current=subprocess.check_output(['git','show','HEAD:'+v['path']]);assert raw==current,('source version split',m)
 checks[m]=dict(module=m,sha256=o['object_sha256'],source=dict(path=v['path'],revision=selected,source_sha256=v['sha256']),authority=v['authority'],original_object_path=plan['workspace']+'/objects/'+m.replace('.','/')+'.olean')
 es=[e for e in edges if e['module']==m]
 assert es,('missing dependency evidence',m)
 for e in es:
  usededges.append(dict(module=m,dependency=e['dependency'],sha256=e['expected']));visit(e['dependency'])
for m in ['R1Z.ProverRwSuccessOptions','R1Z.ProverRwOuterMapErr','R1Z.ProverRwCallerBinding']:visit(m)
payload=dict(checks=list(checks.values()),edges=usededges,base=base)
code='''import json,sys,pathlib,hashlib
x=json.load(sys.stdin);roots=list(map(pathlib.Path,x['base']['LEAN_PATH'].split(':')))
def resolve(m):
 ns=m.split('.')[0];r=next(r for r in roots if (r/ns).is_dir() or ('.' not in m and (r/(m+'.olean')).is_file()))
 p=r/(m.replace('.','/')+'.olean');assert p.is_file(),('first-root missing',m,str(p));return p
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
allchecks=x['checks']+x['base']['project_checks']+x['base']['external_checks'];auth={v['module']:v['sha256'] for v in allchecks}
for v in allchecks:
 p=resolve(v['module']);assert sha(p)==v['sha256'],('cohort conflict',v['module']);v['path']=str(p)
for e in x['edges']:
 assert auth[e['dependency']]==e['sha256'],('edge authority mismatch',e)
 assert sha(resolve(e['dependency']))==e['sha256'],('edge cohort mismatch',e)
copies=[]
for v in x['checks']:
 p=resolve(v['module'])
 if p.is_symlink():
  assert str(p).startswith('/home/dombarker/project-offloads/codex-pv-evh-20261029/objects/')
  origin=str(p.resolve());raw=p.read_bytes();p.unlink();p.write_bytes(raw)
  assert sha(p)==v['sha256']
  copies.append(dict(module=v['module'],origin=origin,path=str(p),sha256=v['sha256']))
print(json.dumps(dict(project_checks=x['checks'],edges=x['edges'],LEAN_PATH=x['base']['LEAN_PATH'],plain_copies=copies,shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
assert r.returncode==0,(r.stderr+r.stdout)[-2000:]
x=json.loads(r.stdout);x['verified_source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();x['authority_revision']=rev;x['source_cohort']='same recorded runjoin61 build instance';(E/'source-binding-extension.json').write_text(json.dumps(x,indent=2)+'\n')
print('PASS source/cohort extension:',len(checks),'project modules;',len(usededges),'edges')
