"""Extend ONLY the SAME runjoin32 cohort to the actual NativeFrames62 closure.
No compilation, shared modification, environment change, or library extension.
Missing project overlay files become hash-checked plain copies under h6.
"""
from pathlib import Path
import json,hashlib,subprocess,shlex
E=Path('evidence/pv-evh8-20261101');rev='7c0b14bc8783687100aa2f62de6698068c8f5360';sha=lambda b:hashlib.sha256(b).hexdigest()
def read(p):return json.loads(subprocess.check_output(['git','show',rev+':'+p]))
plan=read('evidence/pv-runjoin62-20261029/build-plan.json');pre=read('evidence/pv-runjoin62-20261029/fresh-preflight.json');old=json.load(open(E/'source-binding-extension.json'));base=json.load(open('evidence/pv-evh4-20261029/prepare-PV_EVH_World.json'))['result']
objects={v['module']:v for v in pre['projects']};edges={}
for e in pre['dependencies']:edges.setdefault(e['module'],[]).append(e)
known={v['module']:v for v in base['project_checks']+old['project_checks']+base['external_checks']};checks={};used=[]
def visit(m):
 if m in checks:return
 if m in known:
  if m in objects:assert known[m]['sha256']==objects[m]['object_sha256'],('cohort conflict',m)
  return
 v=plan['modules'][m];o=objects[m];assert v['sha256']==o['source_sha256']==o['expected_source_sha256']
 selected=v.get('revision',plan['source_revision']);raw=subprocess.check_output(['git','show',selected+':'+v['path']]);assert sha(raw)==v['sha256'],('source mismatch',m)
 checks[m]=dict(module=m,sha256=o['object_sha256'],source=dict(path=v['path'],revision=selected,source_sha256=v['sha256']),authority=v['authority'],original_object_path=plan['workspace']+'/objects/'+m.replace('.','/')+'.olean')
 es=edges.get(m,[]);assert es,('no dependency evidence',m)
 for e in es:used.append(dict(module=m,dependency=e['dependency'],sha256=e['expected']));visit(e['dependency'])
visit('R1Z.PV_RunJoin_NativeFrames62')
payload=dict(checks=list(checks.values()),known=list(known.values()),edges=used,roots=base['LEAN_PATH'].split(':'))
code='''import pathlib,json,sys,hashlib
x=json.load(sys.stdin);roots=list(map(pathlib.Path,x['roots']));auth={v['module']:v for v in x['known']+x['checks']}
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def destination(m):
 ns=m.split('.')[0];r=next(r for r in roots if (r/ns).is_dir() or ('.' not in m and (r/(m+'.olean')).is_file()))
 return r/(m.replace('.','/')+'.olean')
def input_path(v):
 p=destination(v['module'])
 if p.is_file():return p
 assert v in x['checks'],('missing inherited object',v['module'])
 return pathlib.Path(v['original_object_path'])
for v in auth.values():assert sha(input_path(v))==v['sha256'],('object mismatch',v['module'])
for e in x['edges']:assert auth[e['dependency']]['sha256']==e['sha256'],('edge mismatch',e)
copies=[]
for v in x['checks']:
 dest=destination(v['module']);source=input_path(v).resolve()
 assert str(dest).startswith('/home/dombarker/project-offloads/codex-pv-evh-20261029/objects/')
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  p=source.with_suffix(suffix);q=dest.with_suffix(suffix)
  if not p.is_file():continue
  digest=sha(p)
  if q.exists():assert sha(q)==digest,('companion conflict',v['module'],suffix)
  if not q.is_file() or q.is_symlink():
   raw=p.read_bytes();origin=str(p)
   if q.is_symlink():q.unlink()
   q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(raw)
   copies.append(dict(module=v['module'],path=str(q),origin=origin,sha256=digest))
  assert not q.is_symlink()
 v['path']=str(dest)
for v in auth.values():assert sha(destination(v['module']))==v['sha256']
print(json.dumps(dict(project_checks=x['checks'],edges=x['edges'],plain_copies=copies,shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True);assert r.returncode==0,(r.stderr+r.stdout)[-2000:]
x=json.loads(r.stdout);x['authority_revision']=rev;x['workspace']=plan['workspace'];x['same_cohort']=True
(E/'native-binding-extension.json').write_text(json.dumps(x,indent=2)+'\n')
old['project_checks']+=x['project_checks'];old['edges']+=x['edges'];old['native_extension_revision']=rev;old['verified_source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();(E/'source-binding-extension.json').write_text(json.dumps(old,indent=2)+'\n')
print('PASS actual native closure:',len(checks),'additional same-cohort projects;',len(x['plain_copies']),'plain file copies')
