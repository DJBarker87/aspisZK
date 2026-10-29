from pathlib import Path
import hashlib,json
D=Path('/home/dombarker/project-offloads/codex-pv-diag10-20261029');B=D.parent/'codex-pv-b3p6-20261028'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((D/'b3p-candidate-pins.json').read_text());accepted={}
for p in sorted(B.glob('lean-*/submission.json')):
 r=json.loads(p.read_text());out=p.parent/'receipt/receipt.json'
 if out.exists():
  z=json.loads(out.read_text())
  if z.get('exit_status',z.get('exit',z.get('exit_code')))==0:accepted.setdefault(r['module'],[]).append((p,r,z))
seen={};conflicts=[]
def visit(m,expected=None):
 if m in seen:
  assert expected is None or seen[m]['object_sha256']==expected;return
 own=B/'lean-objects'/(m.replace('.','/')+'.olean')
 if not own.exists():
  return
 candidates=[]
 for p,r,z in accepted.get(m,[]):
  if r['source_sha256']==sha(B/'lean'/(m.replace('.','/')+'.lean')):
   candidates.append((p,r,z))
 assert candidates,(m,'no accepted matching source')
 p,r,z=candidates[-1]
 objsha=sha(own)
 if expected:assert expected==objsha,(m,'dep changed')
 if m in pins:assert sha(B/'lean'/(m.replace('.','/')+'.lean'))==pins[m]['sha256'],m
 dst=D/'b3p-objects'/(m.replace('.','/')+'.olean')
 if dst.exists():assert sha(dst)==objsha,(m,'cohort conflict')
 seen[m]=dict(source_sha256=r['source_sha256'],object_sha256=objsha,submission=str(p),dependencies=r['dependency_objects'])
 for dep,q in r['dependency_objects'].items():
  assert sha(Path(q['path']))==q['sha256'],(m,dep,'changed producer dep')
  if (B/'lean-objects'/(dep.replace('.','/')+'.olean')).exists():visit(dep,q['sha256'])
  else:
   env=json.loads((D/'env-J.json').read_text());effective=next((Path(x)/(dep.replace('.','/')+'.olean') for x in env['LEAN_PATH'].split(':') if (Path(x)/(dep.replace('.','/')+'.olean')).exists()),None)
   if not effective or sha(effective)!=q['sha256']:
    raise AssertionError((m,dep,'external cohort gap'))
 dst.parent.mkdir(parents=True,exist_ok=True)
 for a,b in [(own,dst),(Path(str(own)+'.private'),Path(str(dst)+'.private')),(Path(str(own)+'.server'),Path(str(dst)+'.server')),(own.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if a.exists() and not b.exists():b.symlink_to(a)
visit('PV_B3P_InstalledOk8227')
(D/'b3p-reuse.json').write_text(json.dumps(dict(rows=seen,checked=len(seen)),indent=2)+'\n')
print('b3p verified',len(seen))
