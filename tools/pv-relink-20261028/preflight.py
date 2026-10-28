from pathlib import Path
import subprocess,json,re,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-relink-20261028';D='/home/dombarker/project-offloads/codex-pv-relink-20261028'
def git(*args):return subprocess.check_output(['git',*args],cwd=R)
def sha(x):return hashlib.sha256(x).hexdigest()
ext=json.loads((E/'external-object-manifest.json').read_text()); ex={x['module'].replace('/','.'):x for x in ext}
ej=json.loads((E/'EJR_final-inventory.json').read_text());pins={x['module'].replace('/','.'):x for x in ej['selected'] if x.get('resolution')}
freeze=json.loads(git('show','research:docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/final-source-freeze.json'))
(E/'freeze-input.json').write_text(json.dumps(freeze,indent=2)+'\n')
# Inspectable tracked paths, used only after EJR/freeze precedence.
files=git('ls-files','*.lean').decode().splitlines(); tracked={}
for p in files:
 if '/lean/' in p:tracked.setdefault(p.split('/lean/',1)[1][:-5].replace('/','.'),[]).append(p)
for m,x in json.loads((R/'evidence/pv-cbmid-20261027/LEAN-IMPORT-PROVENANCE.json').read_text()).items():
 tracked['R1Z.'+m]=[x['local_source']]
tracked['R1Z.ProverRwFullFuns']=['docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullFuns.lean']
roots=['R1Z.PV_CBL_PathJoinValue','R1Z.PV_CBL_JoinAdapter','R1Z.PV_CBL_CallbackPublication','R1Z.PV_CBL_StringViewValue','R1Z.PV_CBL_StringByteObservation','R1Z.PV_CBL_AppendSource','R1Z.PV_CB3_Op51Arbitrary','R1Z.PV_AL_SplitSelected','R1Z.PV_AL_SplitBridge']
rows={}
def visit(m):
 if m in rows or m in ex:return
 assert not m.split('.')[-1].startswith('XR'),m
 if m in pins:
  x=pins[m];q=x['resolution'];s=git('cat-file','blob',q['blob']);assert sha(s)==x['sha256'],m
  v=dict(path=q['path'],blob=q['blob'],revision=q['revision'],authority='EJR',sha256=sha(s))
 else:
  # Producer freeze is checked before h5; none of the direct targets is selected from an arbitrary name hit.
  fs=freeze.get('sources',[])
  if isinstance(fs,dict):fs=[dict(module=k,**v) for k,v in fs.items()]
  matches=[x for x in fs if x.get('module','').replace('/','.')==m]
  if matches:
   x=matches[0];p=x.get('path',x.get('source'));s=git('show',freeze.get('revision','f6c2399bb7')+':'+p);assert sha(s)==x['sha256'];v=dict(path=p,sha256=sha(s),authority='freeze')
  else:
   ps=tracked.get(m,[]);assert len(ps)==1,('unresolved',m,ps)
   p=ps[0];s=git('show','HEAD:'+p);assert (R/p).read_bytes()==s,('dirty',p)
   v=dict(path=p,blob=git('rev-parse','HEAD:'+p).decode().strip(),revision=git('rev-parse','HEAD').decode().strip(),sha256=sha(s),authority='h5 tracked HEAD')
 v['imports']=re.findall(r'^import\s+(\S+)',s.decode(),re.M)
 v['tracked_alternatives']=[dict(path=p,sha256=sha(git('show','HEAD:'+p))) for p in tracked.get(m,[])]
 rows[m]=v
 for d in v['imports']:visit(d)
for m in roots:visit(m)
(E/'source-resolution.json').write_text(json.dumps(dict(roots=roots,modules=rows),indent=2)+'\n')
code=r'''
from pathlib import Path
import json,hashlib,re,time
D=Path(DIR);B=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
e=json.loads((B/'r1-privacy-build-integration-20261019/env/J.json').read_text())
# Preserve env-J order; read-only Stream B caches only for missing project modules.
base_roots=[D/'lean-objects',B/'aspis-joint-20261019/objects']+[Path(x) for x in e['LEAN_PATH'].split(':')]
cache=[B/'codex-pv-cblib-20261027/lean-objects',B/'codex-pv-alib-20261027/lean-objects',B/'codex-pv-cb3-20261026/lean-objects']
source_roots=[B/'aspis-joint-20261019/sources',B/'codex-pv-cblib-20261027/lean-sources',B/'codex-pv-alib-20261027/lean-sources',B/'codex-pv-cb3-20261026/lean-sources']
errors=[];er=[]
for x in EXTERNAL:
 p=next((r/(x['module']+'.olean') for r in base_roots if (r/(x['module']+'.olean')).exists()),None)
 h=sha(p) if p else None;ok=h==x['object_sha256'];er.append(dict(module=x['module'],path=str(p),sha256=h,ok=ok))
 if not ok:errors.append(['external',x['module'],str(p),h,x['object_sha256']])
pr={}
for m,x in PROJECT.items():
 rel=m.replace('.','/');q=next((r/(rel+'.lean') for r in source_roots if (r/(rel+'.lean')).exists() and sha(r/(rel+'.lean'))==x['sha256']),None)
 p=next((r/(rel+'.olean') for r in base_roots if (r/(rel+'.olean')).exists()),None)
 if p is None:p=next((r/(rel+'.olean') for r in cache if (r/(rel+'.olean')).exists()),None)
 if q is None or p is None:errors.append(['project missing',m,str(q),str(p)])
 pr[m]=dict(source_path=str(q),source_sha256=sha(q) if q else None,object_path=str(p),object_sha256=sha(p) if p else None)
# Verify cache-prefix imports against our selected objects, including full transitive cone.
for m,x in pr.items():
 if '/lean-objects/' not in x['object_path'] or x['object_path'].startswith(str(D)+'/'):continue
 origin=Path(x['object_path'].split('/lean-objects/')[0]);env=origin/'env-J.json'
 if not env.exists():errors.append(['cache env missing',m,str(env)]);continue
 ce=json.loads(env.read_text());cr=[origin/'lean-objects']+[Path(v) for v in ce['LEAN_PATH'].split(':')]
 if ce['LEAN_GITHASH']!=e['LEAN_GITHASH']:errors.append(['toolchain',m])
 seen=set()
 def check(n):
  if n in seen:return
  seen.add(n)
  if n in PROJECT:
   expect=pr[n]['object_sha256'];ds=PROJECT[n]['imports']
  elif n in EXMAP:expect=EXMAP[n]['object_sha256'];ds=[]
  else:errors.append(['unknown import',n]);return
  p=next((r/(n.replace('.','/')+'.olean') for r in cr if (r/(n.replace('.','/')+'.olean')).exists()),None)
  if p is None or sha(p)!=expect:errors.append(['cache dependency',m,n,str(p)])
  for k in ds:check(k)
 for dep in PROJECT[m]['imports']:check(dep)
 x['cache_dependency_fingerprint_verified']=True;x['original_LEAN_PATH']=ce['LEAN_PATH']
if all(x[0]=='project missing' and x[2]!='None' and x[3]=='None' for x in errors):
 o=D/'lean-objects';o.mkdir(exist_ok=True)
 for m,x in pr.items():
  if x['object_path']=='None':continue
  p=o/(m.replace('.','/')+'.olean');p.parent.mkdir(parents=True,exist_ok=True)
  if not p.exists():p.symlink_to(x['object_path'])
 e['LEAN_PATH']=':'.join([str(o)]+list(map(str,base_roots)))
 (D/'env-J.json').write_text(json.dumps(e,indent=2))
 (D/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
print(json.dumps(dict(ok=not errors,errors=errors,external=er,project=pr,env=e,checked_at=time.time())))
'''.replace('DIR',repr(D)).replace('EXTERNAL',repr(ext)).replace('PROJECT',repr(rows)).replace('EXMAP',repr(ex))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=json.loads(r.stdout);(E/'preflight.json').write_text(json.dumps(j,indent=2)+'\n');print(json.dumps(dict(project=len(rows),external=len(ext),ok=j['ok'],errors=j['errors'])))
