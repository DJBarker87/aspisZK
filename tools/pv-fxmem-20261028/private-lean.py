"""Use the existing run2 runner privately for the missing h5 dependency.
No shared source, object, environment or launcher is changed.
"""
from pathlib import Path
import hashlib,json,re,subprocess,sys,shlex,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-fxmem-20261028';D='/home/dombarker/project-offloads/codex-pv-fxmem-20261028';H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads'
n=int(sys.argv[1]);m=sys.argv[2];assert 35500<=n<=35599
assert not (E/f'{n}.json').exists(), 'attempt already recorded'
assert m.startswith('R1Z/PV_FXM_') or m=='R1Z/PDict_ReserveErrorSource'
if n>=35597:assert 'Audit' in m or 'Closure' in m
p=R/'docs/research/v8-r0-zk-20261009/lean'/(m+'.lean');imports=re.findall(r'^import (\S+)',p.read_text(),re.M)
source=p.read_bytes();sha=hashlib.sha256(source).hexdigest();rev=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip()
assert source==subprocess.check_output(['git','show','HEAD:'+str(p.relative_to(R))])
from datetime import datetime
for previous in [E/f'{n}-pre-admission.json',E/f'lean-{n}/admission-before.json',E/f'lean-{n}/admission-barrier.json']:
 if previous.exists():
  old=json.loads(previous.read_text())
  if old.get('allowed') is False:
   due=datetime.fromisoformat(old['utc']).timestamp()+180
   if time.time()<due:
    print('UNCHARGED cooldown still active',round(due-time.time(),1));sys.exit(78)
authority=json.loads((E/'CARRIER-FUNS-PREFLIGHT.json').read_text());assert authority['ok']
closure={}
def visit(im):
 if not im.startswith('R1Z.') or im in closure:return
 key=im.replace('.','/')
 if key in authority['project']:file=R/authority['project'][key]['path']
 else:
  assert im.startswith('R1Z.PV_FXM_') or im=='R1Z.PDict_ReserveErrorSource',im
  file=R/'docs/research/v8-r0-zk-20261009/lean'/(key+'.lean')
 data=file.read_bytes();rel=str(file.relative_to(R))
 assert data==subprocess.check_output(['git','show','HEAD:'+rel])
 closure[im]=dict(path=rel,sha256=hashlib.sha256(data).hexdigest(),blob=subprocess.check_output(['git','rev-parse','HEAD:'+rel],text=True).strip())
 for dep in re.findall(r'^import (\S+)',data.decode(),re.M):visit(dep)
for im in imports:visit(im)
# Existing admission tool, before uploading any source.
G=B+'/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy'
code=f'mkdir -p {D}/lean-{n}; python3 {G}/reservation.py {D}/lean-{n}/pre-admission.json > {D}/lean-{n}/pre-reservation.log 2>&1; status=$?; cat {D}/lean-{n}/pre-admission.json; exit $status'
r=subprocess.run(['ssh',H,code],text=True,capture_output=True);(E/f'{n}-pre-admission.json').write_text(r.stdout);(E/f'{n}-pre-stderr.log').write_text(r.stderr)
if r.returncode or not json.loads(r.stdout)['allowed']:print('UNCHARGED private pre-admission refusal',r.returncode);sys.exit(r.returncode or 78)
# The same shared-first environment prefix as run-joint, with own private
# outputs first. Only this job's new objects occupy the private directory.
code='''from pathlib import Path
import json,hashlib
b=Path(BASE);d=Path(DIR);e=json.loads((b/'r1-privacy-build-integration-20261019/env/J.json').read_text());shared=b/'aspis-joint-20261019/objects'
e['LEAN_PATH']=str(shared)+':'+e['LEAN_PATH'];(d/'env-private-J.json').write_text(json.dumps(e))
(d/'lean-objects/R1Z').mkdir(parents=True,exist_ok=True);(d/'lean-sources/R1Z').mkdir(parents=True,exist_ok=True)
links={}
for m,x in CLOSURE.items():
 rel=m.replace('.','/')+'.olean';dst=d/'lean-objects'/rel
 if dst.exists() and not dst.is_symlink():
  sp=d/'lean-sources'/(m.replace('.','/')+'.lean')
  assert hashlib.sha256(sp.read_bytes()).hexdigest()==x['sha256'],m
  links[m]=dict(path=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest(),source=x,origin='own private compiled object')
 else:
  sp=b/'aspis-joint-20261019/sources'/(m.replace('.','/')+'.lean');obj=shared/rel
  assert hashlib.sha256(sp.read_bytes()).hexdigest()==x['sha256'] and obj.exists(),m
  dst.parent.mkdir(parents=True,exist_ok=True)
  if not dst.exists():dst.symlink_to(obj)
  links[m]=dict(path=str(dst),sha256=hashlib.sha256(dst.read_bytes()).hexdigest(),source=x,origin=str(obj))
roots=[d/'lean-objects',shared]+[Path(p) for p in e['LEAN_PATH'].split(':')]
deps={}
for m in IMPORTS:
 p=next((r/(m.replace('.','/')+'.olean') for r in roots if (r/(m.replace('.','/')+'.olean')).exists()),None)
 if p is None:raise SystemExit('missing imported object '+m)
 deps[m]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest())
print(json.dumps(dict(env=e,dependencies=deps,linked_project_closure=links)))
'''.replace('BASE',repr(B)).replace('DIR',repr(D)).replace('IMPORTS',repr(imports)).replace('CLOSURE',repr(closure))
r=subprocess.run(['ssh',H,'python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
pre=json.loads(r.stdout)
# Check direct imports against the recorded authority. Their complete closure
# is the carrier preflight + this job's successful, source-pinned receipts.
authority=json.loads((E/'CARRIER-FUNS-PREFLIGHT.json').read_text());assert authority['ok']
ext={x['module']:x['sha256'] for x in authority['external']};proj=authority['project']
for im,obj in pre['dependencies'].items():
 key=im.replace('.','/')
 if key in ext:assert obj['sha256']==ext[key],im
 elif key in proj:assert obj['sha256']==proj[key]['object_sha256'],im
 else:
  # Own successful objects and the separately compiled h5 error carrier.
  assert im.startswith('R1Z.PV_FXM_') or im=='R1Z.PDict_ReserveErrorSource',im
  sources=list(E.glob('*-source.lean.txt'))
  owned=R/'docs/research/v8-r0-zk-20261009/lean'/(key+'.lean')
  assert owned.exists()
  matches=[q for q in sources if q.read_bytes()==owned.read_bytes() and (E/(q.name.split('-')[0]+'.json')).exists() and json.loads((E/(q.name.split('-')[0]+'.json')).read_text())['exit']==0]
  assert matches,('no accepted source pin',im)
meta=dict(id=n,module=m,source_revision=rev,source_sha256=sha,source_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),source_path=str(p.relative_to(R)),private_environment=pre,authority_sha256=hashlib.sha256((E/'CARRIER-FUNS-PREFLIGHT.json').read_bytes()).hexdigest())
(E/f'{n}-submission.json').write_text(json.dumps(meta,indent=2)+'\n');(E/f'{n}-source.lean.txt').write_bytes(source)
subprocess.run(['scp','-q',str(p),H+':'+D+'/lean-sources/'+m+'.lean'],check=True)
cmd=['python3',str(R/'tools/pv-fxmem-20261028/scope.py'),f'lean-{n}','focused private Lean proof/typecheck', 'timeout','900','python3',B+'/aspis-fs-generic-20261006/evidence/run2.py',D+'/env-private-J.json',D+'/lean-objects',D+'/lean-sources',D+'/lean-objects/'+m+'.olean',D+'/lean-sources/'+m+'.lean','7000']
r=subprocess.run(cmd);d=E/f'lean-{n}'
if not (d/'receipt.json').exists():raise SystemExit(r.returncode)
j=json.loads((d/'receipt.json').read_text());log=(d/'output.log').read_text();meta.update(j)
meta['axioms']=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S)
meta['receipt_collection_revision']=j['source_revision'];meta['source_revision']=rev
meta['print_axioms']=meta['axioms'] if meta['axioms'] else 'N/A: inherited type declarations only'
meta['limits']['Lean_M']=7000
meta['accepted']=j['exit']==0 and 'sorryAx' not in log
meta['object_pin']=None
if meta['accepted']:
 q=subprocess.run(['ssh',H,'sha256sum '+D+'/lean-objects/'+m+'.olean'],text=True,capture_output=True);assert q.returncode==0,q.stderr;meta['object_pin']=q.stdout.split()[0]
(E/f'{n}.json').write_text(json.dumps(meta,indent=2)+'\n');print(json.dumps(dict(id=n,exit=j['exit'],accepted=meta['accepted'],axioms=meta['axioms'])))
sys.exit(j['exit'])
