"""Collect restored Env-J receipts with effective (ordered) import provenance."""
from pathlib import Path
import subprocess,hashlib,json,re,sys,shlex
root=Path(__file__).resolve().parents[2];a,module=sys.argv[1:3];out=root/'evidence/pv-op134-20261027';host='dombarker@100.108.41.90';base='/home/dombarker/project-offloads';e=base+'/aspis-fs-generic-20261006/evidence'
def ssh(c):return subprocess.check_output(['ssh',host,c],text=True)
for stem,ext in [('out','log'),('time','log'),('sha','txt')]:
 name=f'{stem}-{a}.{ext}';(out/name).write_text(ssh(f'cat {e}/{name}'))
src=ssh(f'cat {base}/codex-pv-op134-20261027/sources/{module}.lean');imports=re.findall(r'^import (\S+)',src,re.M)
code='''import json,pathlib,hashlib
base=pathlib.Path('/home/dombarker/project-offloads')
env=json.loads((base/'r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[str(base/'codex-pv-op134-20261027/objects')]+env['LEAN_PATH'].split(':')
r={}
for imp in %r:
 for p in paths:
  q=pathlib.Path(p)/(imp.replace('.','/')+'.olean')
  if q.exists():r[imp]={'path':str(q),'sha256':hashlib.sha256(q.read_bytes()).hexdigest()};break
 else:r[imp]={'missing':True}
print(json.dumps(r))
'''%imports
ids=json.loads(ssh('python3 -c '+shlex.quote(code)));log=(out/f'out-{a}.log').read_text();t=(out/f'time-{a}.log').read_text()
def field(p):
 m=re.search(p,t);return m[1] if m else None
r=dict(attempt=int(a),module=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_sha256=hashlib.sha256(src.encode()).hexdigest(),dependency_objects=ids,deps_fingerprint=hashlib.sha256(json.dumps(ids,sort_keys=True).encode()).hexdigest(),exit=int(re.search(r'^exit=(\d+)',log,re.M)[1]),wall=field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=field(r'Maximum resident set size \(kbytes\): (\d+)'),swap=field(r'Swaps: (\d+)'),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",log,re.S),target=['run-joint.sh',a,module,'J','7000','8'],limits=dict(lean_M=7000,MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64),cache_caveat='Restored shared/union objects; direct imports resolved in effective search order. No cb3 lean-objects survived.')
prepath=out/f'{a}-preflight.json'
if prepath.exists():
 pre=json.loads(prepath.read_text());actual=pre['deps_fingerprint'];r['dependency_objects_before_run']=pre['dependency_objects'];r['post_dependency_fingerprint']=r['deps_fingerprint'];r['dependency_identity_changed_during_run']={k:({'missing':True} if v=='MISSING' else v) for k,v in pre['dependency_objects'].items()}!=ids
else:actual='none'
r['actual_launcher_fingerprint']=actual
r['target']=[base+'/codex-pv-op134-20261027/run-joint.sh',a,module,'J','7000','8']+([] if actual=='none' else [actual])
r['source_pin']='source_revision is the actual checkout HEAD; source_sha256 pins the compiled working source, including pre-commit additions.'
if not r['axioms']:r['axioms_status']='N/A extraction-definition rebuild or declaration-only inspection; see downstream audits.'
(out/f'{a}.json').write_text(json.dumps(r,indent=2)+'\n');print(a,r['exit'],r['wall'])
