#!/usr/bin/env python3
"""Isolate the unchanged map helper from unrelated crate initialization/MIR."""
import subprocess,json,os,sys,time,hashlib,fcntl
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit32-20261022')
lock=(H/'isolated-kani.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX)
name,target=sys.argv[1:3]
os.chdir(H/'harness/map-gate')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'kani-isolated-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
while True:
 caps=[]
 for p in Path('/sys/fs/cgroup').rglob('memory.max'):
  try:
   v=p.read_text().strip()
   if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
  except OSError:pass
 if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30:break
 print('Reservation hold for isolated Kani gate',flush=True);time.sleep(30)
files=[H/'src/crates/aspis-r1-cost-probe/src/sim_owned32.rs',H/'harness/publication-kani32-bounded.rs',H/'harness/map-gate/lib.rs',H/'harness/map-gate/Cargo.toml']
(H/(name+'-inputs.json')).write_text(json.dumps(dict(source_revision=(H/'revision.txt').read_text().strip(),source_hashes={str(p.relative_to(H)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files},reservations=caps,scope='Isolated compilation of the exact helper source against the same Kani Rust BTreeMap; no stubs or assumptions added'),indent=2)+'\n')
cmd=['cargo','kani','--no-assertion-reach-checks','-j','4','--lib','--exact','--harness',target,'-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions','--object-bits','10']
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Isolated Kani compilation and native BTreeMap transition; no dense arithmetic; 600 second timeout','--','timeout','600',*cmd]).returncode)
