"""Read-only h6 checks; no compiler launch or shared writes."""
from pathlib import Path
import hashlib,json,lzma,subprocess,shlex,sys
E=Path('evidence/pv-rj4id-20261029');H='/home/dombarker/project-offloads/codex-pv-rj4id-20261029'
sha=lambda b:hashlib.sha256(b).hexdigest()
plan=json.loads((E/'inherited-plan.json').read_text());reuse=json.loads(lzma.decompress((E/'inherited-reuse.json.xz').read_bytes()));own=json.loads((E/'inherited-validation.json').read_text());ejr=json.loads((E/'ejr-authority.json').read_text());ejr={v['module'].replace('/','.'):v for v in reversed(ejr['selected'])}
ref=subprocess.check_output(['git','rev-parse','origin/codex/pv-runjoin-20261026'],text=True).strip();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
projects={v['module']:v for v in reuse['projects']};projects.update({v['module']:v for v in own['checks']});external={v['module'].replace('/','.'):v for v in reuse['external']}
extra=json.loads((E/'extra-records.json').read_text())
plan['modules'].update(extra['modules'])
projects.update(extra['records'])
own['dependencies'] += [dict(module=m,dependency=d,sha256=v['sha256']) for m,r in extra['records'].items() for d,v in r['dependencies'].items()]
roots=sys.argv[1:];visited={};gaps=[]
def visit(m):
 if m in visited or m in external:return
 if m not in plan['modules'] or m not in projects:gaps.append({'module':m,'reason':'not in retained source/object records'});return
 p=plan['modules'][m];path=p['path'];selected=rev;authority='h5 HEAD'
 if m in ejr:
  path=ejr[m]['resolution']['path'];authority='EJR precedence'
 elif m.startswith(('R1Z.PV_RunJoin_','R1Z.PV_RJDec_','R1Z.PV_OWN')):
  selected=ref;authority='user-authorized read-only runjoin ref'
 r=subprocess.run(['git','show',selected+':'+path],capture_output=True)
 if r.returncode:gaps.append({'module':m,'path':path,'reason':'selected source absent','revision':selected});return
 digest=sha(r.stdout)
 if digest!=p['sha256'] or digest!=projects[m]['source_sha256']:
  gaps.append({'module':m,'reason':'selected source differs from retained object source','selected_sha256':digest,'recorded_sha256':p['sha256'],'path':path});return
 visited[m]=dict(module=m,path=path,revision=selected,authority=authority,git_blob=subprocess.check_output(['git','rev-parse',selected+':'+path],text=True).strip(),source_sha256=digest,object_sha256=projects[m].get('expected_object_sha256',projects[m]['object_sha256']),imports=p['imports'],cache='rjdec' if any(v['module']==m for v in own['checks']) else 'runjoin32')
 for d in p['imports']:visit(d)
for m in roots:visit(m)
(E/'source-resolution.json').write_text(json.dumps(dict(roots=roots,runjoin_revision=ref,source_revision=rev,projects=visited,gaps=gaps),indent=2)+'\n')
print('resolved',len(visited),'gaps',gaps)
if gaps:sys.exit(2)
deps=[v for v in reuse['dependencies']+own['dependencies'] if v['module'] in visited]
authority=json.loads((E/'external-authority.json').read_text()); auth={v['module'].replace('/','.'):v['object_sha256'] for v in authority}
assert all(auth[v['module']]==v['expected'] for v in reuse['external'])
payload=dict(H=H,projects=visited,dependencies=deps,external=reuse['external'],ir=reuse['ir'],toolchain=reuse['toolchain'],inherited_prefix=own['LEAN_PATH'])
code=r'''import pathlib,json,sys,hashlib,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['H']);old=pathlib.Path('/home/dombarker/project-offloads/codex-pv-runjoin-20261026/runjoin32-lean');dec=pathlib.Path('/home/dombarker/project-offloads/codex-pv-rjdec-20261028');env=json.load(open(dec/'J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert env['LEAN_PATH']==x['inherited_prefix'];assert env['LEAN_GITHASH']=='8c9756b28d64dab099da31a4c09229a9e6a2ef35';assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()==env['LEAN_GITHASH']
checks=[]
for m,v in x['projects'].items():
 rel=m.replace('.','/');cache=dec if v['cache']=='rjdec' else old;s=cache/'sources'/(rel+'.lean');o=next(q/(rel+'.olean') for q in roots if (q/(rel+'.olean')).is_file())
 assert sha(s)==v['source_sha256'],('source',m);assert sha(o)==v['object_sha256'],('object',m)
 checks.append(dict(module=m,source_sha256=sha(s),object_path=str(o),object_sha256=sha(o)))
for v in x['dependencies']:
 d=v['dependency'];q=next(q/(d.replace('.','/')+'.olean') for q in roots if (q/(d.replace('.','/')+'.olean')).is_file());assert sha(q)==v.get('expected',v['sha256']),('dependency',v)
for v in x['external']:assert sha(pathlib.Path(v['path']))==v['expected'],('external',v)
for v in x['ir']:assert sha(old/'external'/(v['module'].replace('.','/')+'.ir'))==v['expected'],('ir',v)
for n in ['objects','sources','evidence']:(p/n).mkdir(parents=True,exist_ok=True)
env['LEAN_PATH']=str(p/'objects')+':'+env['LEAN_PATH'];(p/'J.json').write_text(json.dumps(env))
print(json.dumps(dict(all_match=True,checks=checks,dependencies=len(x['dependencies']),external=len(x['external']),ir=len(x['ir']),toolchain=env['LEAN_GITHASH'],inherited_prefix=x['inherited_prefix'],LEAN_PATH=env['LEAN_PATH'],shared_written=False)))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(payload),text=True,capture_output=True)
(E/'h6-result.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr,result=json.loads(r.stdout) if r.returncode==0 else r.stdout),indent=2)+'\n');print(r.stderr or r.stdout[:1000]);sys.exit(r.returncode)
