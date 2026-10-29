from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag9-20261029');R=D.parent/'codex-pv-rj4idb-20261029'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
accepted={}
for p in sorted((R/'evidence').glob('results-*.json')):
 for r in json.loads(p.read_text()):
  if r.get('accepted') and r['exit']==0:accepted[r['module']]=r
expected=json.loads((D/'decoder-source-pins.json').read_text());seen={}
external={r['module'].replace('/','.'):r for r in json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())}
def visit(m):
 if m in seen:return
 if m in external:
  r=external[m];assert sha(Path(r['path']))==r['object_sha256'];return
 r=accepted[m];src=R/'sources'/(m.replace('.','/')+'.lean');obj=R/'objects'/(m.replace('.','/')+'.olean')
 assert sha(src)==r['source_sha256']==expected[m]['sha256'],m
 assert sha(obj)==r['object_sha256'],m
 seen[m]=r
 for dep,q in r['dependencies'].items():
  assert sha(Path(q['path']))==q['sha256'];visit(dep)
 dst=D/'objects'/(m.replace('.','/')+'.olean');dst.parent.mkdir(parents=True,exist_ok=True)
 if dst.exists():assert sha(dst)==sha(obj)
 else:dst.symlink_to(obj)
 for a,b in [(Path(str(obj)+'.private'),Path(str(dst)+'.private')),(Path(str(obj)+'.server'),Path(str(dst)+'.server')),(obj.with_suffix('.ir'),dst.with_suffix('.ir'))]:
  if a.exists() and not b.exists():b.symlink_to(a)
visit('PV_RJ4IDB_OpenInputs')
(D/'decoder-reuse.json').write_text(json.dumps(dict(rows=seen,checked=len(seen),boundary='h6 read-only exact candidate sources / accepted rj4idb objects / recursive import fingerprints / same 4.32 toolchain / identical effective objects'),indent=2)+'\n')
print('decoder closure',len(seen))
