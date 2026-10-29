from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-skwb-20261029');P=D.parent;O=P/'codex-pv-skw-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
env=json.loads((O/'env-l1.json').read_text()); paths=[Path(p) for p in env['LEAN_PATH'].split(':')]; ownpaths=[Path(p) for p in json.loads((O/'env-own.json').read_text())['LEAN_PATH'].split(':') if Path(p)!=O/'objects']; paths+= [p for p in ownpaths if p not in paths]
def select(m):return next((p/(m.replace('.','/')+'.olean') for p in [D/'objects']+paths if (p/(m.replace('.','/')+'.olean')).is_file()),None)
staged={}
def stage(m,p,h):
 assert sha(p)==h,(m,p)
 q=D/'objects'/(m.replace('.','/')+'.olean');q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert sha(q)==h,('conflict',m)
 for a,b in [(p,q),(Path(str(p)+'.server'),Path(str(q)+'.server')),(Path(str(p)+'.private'),Path(str(q)+'.private')),(p.with_suffix('.ir'),q.with_suffix('.ir'))]:
  if a.is_file() and not b.exists():b.symlink_to(a)
 staged[m]=dict(path=str(p),sha256=h,companions={str(a):sha(a) for a in [Path(str(p)+'.server'),Path(str(p)+'.private'),p.with_suffix('.ir')] if a.exists()})
pin=json.loads((P/'codex-pv-l1g-20261029/CACHE-PIN.json').read_text());assert sha(O/'l1g-final-validation.json')==pin['final_validation_sha256']
h6=json.loads((O/'l1g-final-validation.json').read_text())['h6_final'];assert h6['all_match']
for r in h6['checks']:stage(r['module'],Path(r['path']),r['sha256'])
# DIAG and accepted witnesses must match their original complete direct import fingerprints.
for tag,group in json.loads((O/'reuse.json').read_text()).items():
 for m,r in group['rows'].items():
  if not r.get('external'):stage(m,Path(r['object']),r['sha256'])
for n in [68704,68708,68709,68710]:
 r=json.loads((O/f'lean{n}-receipt.json').read_text());assert r['exit']==0
 for m,hs in r['dependency_objects'].items():
  h=next(v for k,v in hs.items() if k.endswith('.olean'));assert sha(select(m))==h,(n,m)
 stage(r['module'],O/'objects'/(r['module'].replace('.','/')+'.olean'),r['object_sha256'])
plan=json.loads((O/'own-plan.json').read_text());missing=[];reuse=[]
# Reuse all own rows if their entire recorded cohort matches, otherwise rebuild privately.
for r in list(plan['reused'].values())+plan['build']:
 m=r['module'];p=select(m)
 if p and sha(p)==r['object_sha256'] and all(select(k) and sha(select(k))==v for k,v in r['dependency_objects'].items()):
  stage(m,p,r['object_sha256']);reuse.append(m)
 else:
  src=Path(r.get('source',str(P/'codex-pv-ownc-20261029/lean-sources'/(m.replace('.','/')+'.lean'))))
  assert sha(src)==r['source_sha256'],m
  q=D/'sources'/(m.replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,q)
  missing.append(dict(r,module=m))
ext=json.loads((P/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert sha(select(r['module'].replace('/','.')))==r['object_sha256'],r['module']
env['LEAN_PATH']=str(D/'objects')+':'+':'.join(str(p) for p in paths if p!=O/'objects');(D/'env-J.json').write_text(json.dumps(env,indent=2)+'\n')
(D/'staging.json').write_text(json.dumps(dict(staged=staged,own_reused=reuse,build=missing,external_checked=len(ext),old_l1_cache_pin=pin),indent=2)+'\n')
(D/'environment-corrections.json').write_text(json.dumps({'68707':dict(failure_class='pre-elaboration environment',error="missing R1Z.PV_OWN_Heap in selected private package",correction='stage full verified L1 cohort with all companions and compatible own objects under one private package root',evidence='staging.json')},indent=2)+'\n')
print('staged',len(staged),'own reused',len(reuse),'missing',len(missing));print([r['module'] for r in missing])
