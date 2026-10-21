#!/usr/bin/env python3
"""One capped Kani target, no SHA-256 assumptions; unwinding checks enabled."""
import os, sys, json, subprocess, hashlib, time, fcntl
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit29-20261022')
lane=int(os.environ.get('PROVER_KANI_LANE','0')); assert lane in range(3)
worker_lock=(H/f'rust-worker-lane{lane}.lock').open('a')
fcntl.flock(worker_lock,fcntl.LOCK_EX)
name,target=sys.argv[1:3]
os.chdir(H/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'], CARGO_TARGET_DIR=str(H/('kani-contract-target' if lane==0 else f'kani-lane{lane}-target')), CARGO_BUILD_JOBS='4', CARGO_NET_OFFLINE='true', RUSTFLAGS='-C link-arg=-Wl,--threads=4')
def reservation():
    caps=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip(): caps.append(dict(path=str(p.parent),bytes=int(v)))
        except OSError: pass
    return caps
caps=reservation()
while sum(x['bytes'] for x in caps)+8*2**30 > 55*2**30:
    print('Reservation hold:', sum(x['bytes'] for x in caps)/2**30, '+ 8 GiB', flush=True)
    time.sleep(30)
    caps=reservation()
(H/(name+'-inputs.json')).write_text(json.dumps(dict(reservations=caps,source_revision=(H/'revision.txt').read_text().strip(),source_hashes={str(p.relative_to(H/'src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in list((H/'src/crates/aspis-prover/src').glob('*.rs'))+list((H/'src/crates/aspis-core/src').rglob('*.rs'))+list((H/'src/crates/aspis-r1-cost-probe/src').glob('*.rs'))+[H/'src/Cargo.lock',H/'src/crates/aspis-prover/Cargo.toml',H/'src/crates/aspis-core/Cargo.toml']}),indent=2)+'\n')
cmd=['cargo','kani','--no-assertion-reach-checks','-j','4','-p','aspis-r1-cost-probe','--lib','--exact','--harness',target,'-Z','function-contracts','-Z','stubbing','-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions']
unwindset=os.environ.get('KANI_UNWINDSET')
if unwindset: cmd += ['--unwindset',unwindset]
solver=os.environ.get('KANI_SOLVER')
if solver:
    assert solver in ['kissat','cadical']
    cmd[2:2]=['--solver',solver]
if target.startswith(('state_only_hiding::','state_only_entropy::')):
    cmd[cmd.index('-p')+1]='aspis-prover'
    cmd[cmd.index('--lib'):cmd.index('--lib')]=['--features','r0']
if target.startswith(('sim::','r1_wire::')):
    cmd[cmd.index('--lib'):cmd.index('--lib')]=['--features','r1p-check']
if target.endswith('*'):
    cmd.remove('--exact');cmd[cmd.index('--harness')+1]=target[:-1]
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Kani compilation then bounded relational byte-oracle comparison; no dense arithmetic; 600 second timeout','--','timeout','600',*cmd]).returncode)
