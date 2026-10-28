"""Restore only source-resolved and completely fingerprinted Stream B objects.
Includes public/private import edges; external objects are never rebuilt.
"""
from pathlib import Path
import json,subprocess,hashlib,shlex
R=Path(__file__).resolve().parents[2]; E=R/'evidence/pv-l2c-20261028/resume-d355'; H='/home/dombarker/project-offloads/codex-pv-l2c-20261028'
r=json.load(open(E/'focused-resolution.json')); assert not r['unpinned'];res=r['resolved']
old=json.load(open(R/'evidence/pv-l2c-20261028/private-cache-h6.json'))['source_and_import_fingerprints']
replay=json.loads(subprocess.check_output(['git','show',r['research_revision']+':evidence/pv-replay-20261027/receipts/final-integrity.json']))
replay={x['module'].replace('/','.'):x for x in replay['project_results']}
ext={m:x for m,x in res.items() if 'imports' not in x}; candidates={};bad=set()
for m,x in res.items():
 if m in ext:continue
 if m in old and old[m]['expected_sha256']==x['sha256']:
  o=old[m]; candidates[m]=dict(path=o['object_realpath'],sha256=o['object_sha256'],authority='prior h6 source/object receipt',prior_fingerprint=o['complete_direct_fingerprint'])
 elif m in replay and replay[m]['source_sha256']==x['sha256']:
  o=replay[m];candidates[m]=dict(path='/home/dombarker/project-offloads/codex-pv-replay-20261027/objects/'+m.replace('.','/')+'.olean',sha256=o['object_sha256'],authority='coherent replay final-integrity',prior_fingerprint={})
 else:bad.add(m)
# Require identical transitive object selection to the recorded cache. New public
# edges use the coherent replay record that compiled those exact source bytes.
for m,c in candidates.items():
 deps={}
 for d in res[m]['imports']:
  if d in ext:want=ext[d]['object_sha256']
  elif d in candidates:want=candidates[d]['sha256']
  else:bad.add(m);continue
  deps[d]=want
  if d in c['prior_fingerprint'] and c['prior_fingerprint'][d]!=want:bad.add(m)
  if d not in c['prior_fingerprint'] and d not in ext:
   assert d in replay and replay[d]['object_sha256']==want,(m,d)
 c['complete_direct_fingerprint']=deps;c['source_resolution']=res[m]
while True:
 more={m for m,x in res.items() if any(d in bad for d in x.get('imports',[]))}
 if more<=bad:break
 bad|=more
clean={m:c for m,c in candidates.items() if m not in bad}
code=r'''import sys,json,pathlib,hashlib
rows=json.load(sys.stdin);H=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2c-20261028/lean');checks=[]
e=json.load(open(H/'J.json'));base=json.load(open('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json'));assert all(v==base.get(k) for k,v in e.items() if k!='LEAN_PATH')
for m,c in rows.items():
 p=pathlib.Path(c['path']); assert p.is_file(),(m,str(p));assert hashlib.sha256(p.read_bytes()).hexdigest()==c['sha256'],m
 for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
  q=pathlib.Path(str(p)[:-6]+suffix)
  if not q.is_file():continue
  dest=H/'objects'/(m.replace('.','/')+suffix);dest.parent.mkdir(parents=True,exist_ok=True)
  if dest.exists() or dest.is_symlink():assert dest.is_file() and hashlib.sha256(dest.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest(),str(dest)
  else:dest.symlink_to(q.resolve())
 checks.append(dict(module=m,path=str(p),sha256=c['sha256']))
# Complete selected direct fingerprint, using exactly the private view.
roots=[pathlib.Path(x) for x in e['LEAN_PATH'].split(':')]
for m,c in rows.items():
 for d,h in c['complete_direct_fingerprint'].items():
  q=next(root/(d.replace('.','/')+'.olean') for root in roots if (root/(d.replace('.','/')+'.olean')).is_file());assert hashlib.sha256(q.read_bytes()).hexdigest()==h,(m,d)
print(json.dumps(dict(toolchain_match=True,checked=checks)))
'''
p=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(clean),text=True,capture_output=True);assert p.returncode==0,p.stderr
(E/'restored-cache.json').write_text(json.dumps(dict(receipt=json.loads(p.stdout),source_and_complete_fingerprints=clean),indent=2)+'\n')
order=[];seen=set()
def visit(m):
 if m in seen or m not in bad:return
 seen.add(m)
 for d in res[m]['imports']:visit(d)
 order.append(m)
visit('PV_L2C_FocusedReplay');assert set(order)==bad
(E/'rebuild-order.json').write_text(json.dumps(order,indent=2)+'\n');print('Restored',len(clean),'project objects; missing objects require',len(order),'serial compiles:',order)
