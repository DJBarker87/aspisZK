#!/usr/bin/env python3
"""Collect text-only receipts and exact scratch diffs; never collect binaries or keys."""
from pathlib import Path
import subprocess,json,difflib,hashlib
E=Path('docs/research/100bit-spend-path-20261013/evidence/prover-speed-20261022');E.mkdir(exist_ok=True,parents=True)
H='/home/dombarker/project-offloads/codex-cx-prover-speed-20261022';host='dombarker@100.108.41.90'
subprocess.run(['scp','-r',host+':'+H+'/receipts',str(E)],check=True)
for mode,rev in [('research','7f13d411b8f6af7dbd17d23e79fd24bf9998e913'),('v2','2b7a80b65a')]:
 for name in [mode+'-source-pins.json',mode+'-sha-disassembly.txt']:
  subprocess.run(['scp',host+':'+H+'/'+name,str(E/name)],check=True)
 pins=json.loads((E/(mode+'-source-pins.json')).read_text());diff=[]
 paths=['crates/aspis-r1-cost-probe/src/'+p for p in ['lib.rs','prover.rs','host_semantic.rs','host_sumcheck.rs','host_commitment.rs','multiproof.rs','weights.rs','transcript.rs','r1_wire.rs','speed_prof.rs']]+['crates/aspis-r1-cost-probe/examples/speed_profile.rs','crates/aspis-prover/src/state_only_entropy.rs','docs/research/v8-r0-zk-20261009/z4/z9e.rs']
 for p in paths:
  old=subprocess.run(['git','show',rev+':'+p],text=True,capture_output=True).stdout
  new=subprocess.check_output(['ssh',host,'cat '+H+'/'+mode+'/'+p],text=True)
  assert hashlib.sha256(new.encode()).hexdigest()==pins[p],p
  diff.extend(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='a/'+p,tofile='b/'+p))
 (E/(mode+'-scratch.patch')).write_text(''.join(diff))
for name in ['admission.json','tools-pins.json']:
 subprocess.run(['scp',host+':'+H+'/'+name,str(E/name)],check=True)
subprocess.run(['scp',host+':'+H+'/tools/host_job-initial.py',str(E/'host_job-initial.py.txt')],check=True)
