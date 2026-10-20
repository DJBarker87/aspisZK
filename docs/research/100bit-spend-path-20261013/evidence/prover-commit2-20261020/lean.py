#!/usr/bin/env python3
"""Install only this job's new modules and run one assigned env J attempt."""
import subprocess,sys,os
from pathlib import Path
module,attempt=sys.argv[1:3]
wait_cap="--wait" in sys.argv[3:]
memory_gib=int(os.environ.get("PROVER_LEAN_MEMORY_GIB","4"))
assert 4<=memory_gib<=7
assert 8100<=int(attempt)<=8399
rel=module.replace('.','/')+'.lean'
p=Path('docs/research/v8-r0-zk-20261009/lean')/rel
host='dombarker@100.108.41.90'
R='/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020'
subprocess.run(['scp',str(p),host+':'+R+'/incoming.lean'],check=True,stdout=subprocess.DEVNULL)
code='''import hashlib,json,re,subprocess,time
from pathlib import Path
R=Path(%r);J=Path('/home/dombarker/project-offloads/aspis-joint-20261019')
rel=%r;attempt=%r;memory_gib=%r
p=J/'sources'/rel
assert rel.startswith('AspisR1ProverCommit/') or rel.startswith('AspisR1ProverLeaf/') or rel.startswith('AspisR1ProverStreams/') or rel.startswith('R1Z/ProverCommit')
p.parent.mkdir(parents=True,exist_ok=True)
if p.exists():
 q=R/'snapshots'/attempt/rel;q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(p.read_bytes())
 o=J/'objects'/Path(rel).with_suffix('.olean')
 if o.exists():q.with_suffix('.olean').write_bytes(o.read_bytes())
p.write_bytes((R/'incoming.lean').read_bytes())
env=json.loads(Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/env/J.json').read_text())
paths=[J/'objects']+[Path(x) for x in env['LEAN_PATH'].split(':')]
deps=[]
seen=set()
def visit(m):
 if m in seen:return
 seen.add(m)
 r=Path(m.replace('.','/')+'.olean')
 o=next((d/r for d in paths if (d/r).exists()),None)
 assert o,m
 deps.append((m,hashlib.sha256(o.read_bytes()).hexdigest()))
 q=J/'sources'/Path(m.replace('.','/')+'.lean')
 if q.exists() and m.startswith(('AspisR1ProverCommit.','AspisR1ProverStreams.','AspisR1ProverLeaf.','R1Z.ProverCommit')):
  for child in re.findall(r'^import (\\S+)',q.read_text(),re.M):visit(child)
for m in re.findall(r'^import (\\S+)',p.read_text(),re.M):visit(m)
deps.sort()
def reservation_total():
 caps=[]
 for c in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=c.read_text().strip()
   if v!='max' and (c.parent/'cgroup.procs').read_text().strip():caps.append(int(v))
  except OSError:pass
 return sum(caps)
start=time.monotonic()
while reservation_total()+memory_gib*2**30>55*2**30:
 assert %r and time.monotonic()-start<600, ('reservation hold',reservation_total()/2**30)
 if time.monotonic()-start<1:print('Waiting for a capped Lean reservation; no compiler launched.',flush=True)
 time.sleep(15)
fp=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest()
(R/('lean-'+attempt+'.json')).write_text(json.dumps(dict(module=rel,attempt=int(attempt),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),deps=deps,deps_fingerprint=fp,deps_fingerprint_scheme="own-cone-transitive-objects-v2",memory_limit_mib=7000,cgroup_memory_max_gib=memory_gib),indent=2)+'\\n')
subprocess.run(['sh','/home/dombarker/project-offloads/r1-privacy-build-integration-20261019/tools/run-joint.sh',attempt,rel[:-5],'J','7000',str(memory_gib),fp],check=True)
'''%(R,rel,attempt,memory_gib,wait_cap)
subprocess.run(['ssh',host,'python3 -'],input=code,text=True,check=True)
