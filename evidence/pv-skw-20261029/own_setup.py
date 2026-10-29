from pathlib import Path
import json,hashlib,shutil
D=Path('/home/dombarker/project-offloads/codex-pv-skw-20261029');P=D.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
old=P/'codex-pv-ownn-20261029';env=json.loads((old/'env-J.json').read_text());paths=[P/'codex-pv-ownh-20261029/lean-objects',P/'codex-pv-ownd-20261029/lean-objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
plan=json.loads((D/'own-plan.json').read_text());ext=json.loads((P/'codex-pv-diag5-20261029/external-authority.json').read_text());ex={r['module'].replace('/','.'):r for r in ext}
def select(m):return next(p/(m.replace('.','/')+'.olean') for p in paths if(p/(m.replace('.','/')+'.olean')).is_file())
for m,r in ex.items():assert sha(select(m))==r['object_sha256'],('external mismatch',m)
for r in list(plan['reused'].values())+plan['build']:
 for m,h in r['dependency_objects'].items():
  if m not in plan['reused'] and m not in {r['module'] for r in plan['build']}:
   assert m in ex,('unpinned project',m)
for m,r in plan['reused'].items():
 assert sha(select(m))==r['object_sha256']
 for dep,h in r['dependency_objects'].items():assert sha(select(dep))==h,(m,dep)
for r in plan['build']:
 q=D/'sources'/(r['module'].replace('.','/')+'.lean');q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(r['source'],q)
env['LEAN_PATH']=str(D/'objects')+':'+':'.join(map(str,paths));(D/'env-own.json').write_text(json.dumps(env,indent=2)+'\n')
(D/'own-preflight.json').write_text(json.dumps(dict(external_checked=len(ex),reused=len(plan['reused']),build=len(plan['build']),source='ownn/ownc final fingerprint; all external imports match h4',toolchain=env['LEAN_GITHASH']),indent=2)+'\n')
print('own external/reused/source pins checked')
