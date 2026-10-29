"""Read-only h6 closure verification for the inherited observation interface."""
from pathlib import Path
import json,hashlib,subprocess,shlex,lzma,re
E=Path('evidence/pv-l1d-20261029');H='/home/dombarker/project-offloads/codex-pv-l1d-20261029'
old=Path('evidence/pv-rj4idb-20261029'); rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
res=json.load(open(old/'source-resolution.json'))['projects']; checks={v['module']:v for v in json.load(open(old/'h6-result.json'))['result']['checks']}
plan=json.load(open(old/'build-plan.json'))['modules'];fresh={v['module']:v for v in json.load(open(old/'final-validation.json'))['checks']}
reuse=json.loads(lzma.decompress(Path('evidence/pv-rj4id-20261029/inherited-reuse.json.xz').read_bytes()));external={v['module'].replace('/','.'):v for v in reuse['external']}
auth={v['module'].replace('/','.'):v['object_sha256'] for v in json.load(open('evidence/pv-rj4id-20261029/external-authority.json'))}
assert all(auth[m]==v['expected'] for m,v in external.items())
selected={};gaps=[];edges=[]
def visit(m):
 if m in selected or m in external:return
 if m in fresh:
  s=plan[m];v=fresh[m];obj='/home/dombarker/project-offloads/codex-pv-rj4idb-20261029/objects/'+m.replace('.','/')+'.olean';deps=v['dependencies'];srcsha=s['sha256'];p=s['path'];imports=s['imports'];authority='h5 inherited git source'
 elif m in res:
  s=res[m];v=checks[m];obj=v['object_path'];p=s['path'];srcsha=s['source_sha256'];imports=s['imports'];deps={};authority=s['authority']
 else:gaps.append(dict(module=m,reason='not in inherited source/object authority'));return
 b=subprocess.run(['git','show',rev+':'+p],capture_output=True)
 if b.returncode or hashlib.sha256(b.stdout).hexdigest()!=srcsha:
  gaps.append(dict(module=m,path=p,reason='HEAD/source authority mismatch',expected=srcsha,actual=hashlib.sha256(b.stdout).hexdigest() if b.returncode==0 else None));return
 selected[m]=dict(module=m,path=p,source_revision=rev,git_blob=subprocess.check_output(['git','rev-parse',rev+':'+p],text=True).strip(),source_sha256=srcsha,object_path=obj,object_sha256=v['object_sha256'],imports=imports,authority=authority)
 for d,r in deps.items():edges.append(dict(module=m,dependency=d,sha256=r['sha256']))
 for d in imports:visit(d)
for m in ['PV_RJ4IDB_OpenInputs','R0Z.AbsorptionLaw','R0Z.LawTransport']:visit(m)
# Recorded dependency hashes from the retained entire transitive cohort.
for f in ['evidence/pv-rj4id-20261029/inherited-validation.json']:
 for v in json.load(open(f))['dependencies']:
  if v['module'] in selected:edges.append(v)
for v in reuse['dependencies']:
 if v['module'] in selected:edges.append(v)
extra=json.load(open('evidence/pv-rj4id-20261029/extra-records.json'))
for m,r in extra['records'].items():
 if m in selected:
  edges.extend(dict(module=m,dependency=d,sha256=v['sha256']) for d,v in r['dependencies'].items())
(E/'source-resolution.json').write_text(json.dumps(dict(revision=rev,projects=selected,gaps=gaps,edges=edges),indent=2)+'\n')
print('source closure',len(selected),'gaps',gaps,flush=True)
if gaps:raise SystemExit(2)
code=r'''import json,sys,pathlib,hashlib,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['H']);base=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rj4idb-20261029');env=json.load(open(base/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
loaded=lambda m:next(q/(m.replace('.','/')+'.olean') for q in roots if (q/(m.replace('.','/')+'.olean')).is_file())
for m,v in x['projects'].items():assert sha(loaded(m))==v['object_sha256'],('object',m)
for v in x['edges']:assert sha(loaded(v['dependency']))==v.get('expected',v.get('sha256')),('edge',v)
for v in x['external']:
 assert sha(pathlib.Path(v['path']))==v['expected'],('external',v)
 assert sha(loaded(v['module'].replace('/','.')))==v['expected'],('external shadow',v)
for n in ['sources','objects','evidence']:(p/n).mkdir(parents=True,exist_ok=True)
# Same inherited prefix; the sole new prefix contains only this job's modules.
original=env['LEAN_PATH'];env['LEAN_PATH']=str(p/'objects')+':'+original;(p/'J.json').write_text(json.dumps(env))
print(json.dumps(dict(all_match=True,projects=len(x['projects']),edges=len(x['edges']),external=len(x['external']),toolchain=env['LEAN_GITHASH'],inherited_prefix=original,LEAN_PATH=env['LEAN_PATH'],shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,projects=selected,edges=edges,external=list(external.values()))),text=True,capture_output=True)
(E/'h6-result.json').write_text(json.dumps(dict(exit=r.returncode,stdout=r.stdout,stderr=r.stderr),indent=2)+'\n');print(r.stdout,r.stderr);raise SystemExit(r.returncode)
