"""Read-only h6 verification of diagnostic receipts against this selected cohort."""
from pathlib import Path
import json,subprocess,shlex,hashlib
E=Path('evidence/pv-l1g-20261029'); H='/home/dombarker/project-offloads/codex-pv-l1g-20261029'
mods={m:v for m,v in json.load(open(E/'focused-resolution.json'))['resolved'].items() if 'imports' in v}
candidates={}
for dirname in ['pv-diag2-20261029','pv-diag10-20261029']:
 for p in sorted(Path('evidence',dirname).glob('lean*-receipt.json')):
  d=json.load(open(p));m=d.get('module')
  if d.get('exit')==0 and m in mods and d.get('source_sha256')==mods[m]['sha256'] and d.get('object_sha256'):
   candidates[m]=dict(receipt=str(p),receipt_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),**d)
for v in json.load(open('evidence/pv-rj4idb-20261029/final-validation.json'))['checks']:
 m=v['module']
 if m in mods and v['source_sha256']==mods[m]['sha256']:
  candidates[m]=dict(module=m,receipt='evidence/pv-rj4idb-20261029/final-validation.json',source_sha256=v['source_sha256'],object_sha256=v['object_sha256'],dependency_objects={d:{r['path']:r['sha256']} for d,r in v['dependencies'].items()},command=['/home/dombarker/project-offloads/codex-pv-rj4idb-20261029/objects/'+m.replace('.','/')+'.olean','source','7000'])
code=r'''import sys,json,pathlib,hashlib,subprocess
x=json.load(sys.stdin);p=pathlib.Path(x['H']);env=json.load(open(p/'retry-J.json'));roots=[pathlib.Path(q) for q in env['LEAN_PATH'].split(':')];sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
assert subprocess.check_output([env['LEAN'],'--githash'],text=True).strip()=='8c9756b28d64dab099da31a4c09229a9e6a2ef35'
loaded=lambda m:next((q/(m.replace('.','/')+'.olean') for q in roots if (q/(m.replace('.','/')+'.olean')).is_file()),None)
for v in x['external']:assert sha(pathlib.Path(v['path']))==v['object_sha256'],('external',v)
accepted=[];pending=dict(x['candidates']);refused={}
while pending:
 progress=False
 for m,v in list(pending.items()):
  if loaded(m) and sha(loaded(m))!=v['object_sha256']:del pending[m];continue
  deps=v['dependency_objects'];reasons=[]
  for d,paths in deps.items():
   q=loaded(d)
   if q is None or sha(q) not in paths.values():reasons.append(d)
  if reasons:refused[m]=reasons;continue
  possible=[pathlib.Path(v['command'][-3]),pathlib.Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029/objects')/(m.replace('.','/')+'.olean')]
  obj=next((q for q in possible if q.is_file() and sha(q)==v['object_sha256']),None)
  if obj is None:refused[m]=['object absent'];continue
  src=p/'sources'/(m.replace('.','/')+'.lean');assert sha(src)==v['source_sha256']
  dest=p/'objects'/(m.replace('.','/')+'.olean');dest.parent.mkdir(parents=True,exist_ok=True)
  for suffix in ['.olean','.olean.private','.olean.server','.ilean','.ir']:
   a=obj.with_suffix(suffix);b=dest.with_suffix(suffix)
   if a.is_file() and not b.exists():b.symlink_to(a)
  accepted.append(dict(object_path=str(obj),**v));del pending[m];progress=True
 if not progress:break
(p/'J.json').write_text(json.dumps(env))
print(json.dumps(dict(accepted=accepted,not_reused={m:refused.get(m) for m in pending},external_verified=len(x['external']),toolchain=env['LEAN_GITHASH'],prefix=env['LEAN_PATH'])))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(dict(H=H,candidates=candidates,external=json.load(open(E/'external-authority.json')))),text=True,capture_output=True)
(E/'supplement-transport.json').write_text(json.dumps(dict(exit=r.returncode,stderr=r.stderr)))
assert r.returncode==0,r.stderr
(E/'supplement-reuse.json').write_text(r.stdout)
x=json.loads(r.stdout);print('Supplement reused',len(x['accepted']),'remaining diagnostic gaps',x['not_reused'])
