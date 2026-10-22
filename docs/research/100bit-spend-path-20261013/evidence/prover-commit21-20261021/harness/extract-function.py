#!/usr/bin/env python3
"""Attempt actual shipped simulator extraction; stop on invalid lowering."""
import os,sys,json,hashlib,subprocess,time,fcntl
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit21-20261021')
CHARON='/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon'
AENEAS='/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static'
worker_lock=(H/'extract-worker.lock').open('a')
fcntl.flock(worker_lock,fcntl.LOCK_EX)
os.chdir(H/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(H/'charon-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4 --cfg aeneas_ref')
def run(name,cmd):
 while True:
  caps=[]
  for p in Path('/sys/fs/cgroup').rglob('memory.max'):
   try:
    v=p.read_text().strip()
    if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append(dict(path=str(p.parent),bytes=int(v)))
   except OSError:pass
  if sum(x['bytes'] for x in caps)+8*2**30<=55*2**30: break
  print('Reservation hold',flush=True);time.sleep(30)
 pins=dict(source_hashes={str(p.relative_to(H/'src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'src').rglob('*.rs')},source_revision=(H/'revision.txt').read_text().strip(),reservations=caps,sha256={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [Path(CHARON),Path(AENEAS),H/'src/crates/aspis-prover/src/prover_commit_reference.rs']})
 (H/(name+'-inputs.json')).write_text(json.dumps(pins,indent=2)+'\n')
 rc=subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Optimized compilation and actual simulator translation; no dense arithmetic or simulator execution','--',*cmd]).returncode
 if rc:raise SystemExit(rc)
name,root,namespace=sys.argv[1:4]
(H/'extraction').mkdir(exist_ok=True)
opaque=[]
for pattern in sys.argv[4:]:opaque+=['--opaque',pattern]
run(name+'-charon',[CHARON,'cargo','--preset','aeneas','--mir','built','--sysroot','default',
 '--start-from',root,
 '--include','core::result::Result', '--include','aspis_core::field', '--include','aspis_core::r0_transcript::CircleRow', '--include','aspis_core::r0::scalar', '--opaque','aspis_core',*opaque,
 '--dest-file',str(H/'extraction'/(name+'.llbc')),'--','--manifest-path',str(H/'src/crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--features','r1p-check','--jobs','4'])
p=H/'extraction'/(name+'.llbc');data=json.loads(p.read_text());(H/(name+'-llbc.json')).write_text(json.dumps(dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),size_bytes=p.stat().st_size,has_errors=data.get('has_errors'),root=root,opaque=sys.argv[4:]),indent=2)+'\n')
assert data['has_errors'] is False
run(name+'-aeneas',[AENEAS,'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(H/'extraction'/('generated-'+name)),'-subdir',namespace,'-split-files','-emit-json',str(p)])
