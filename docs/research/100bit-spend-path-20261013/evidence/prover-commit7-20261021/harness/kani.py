#!/usr/bin/env python3
"""One capped Kani target, no SHA-256 assumptions; unwinding checks enabled."""
import os, sys, json, subprocess, hashlib, time
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-prover-commit7-20261021')
name,target=sys.argv[1:3]
os.chdir(H/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'], CARGO_TARGET_DIR=str(H/'kani-contract-target'), CARGO_BUILD_JOBS='4', CARGO_NET_OFFLINE='true', RUSTFLAGS='-C link-arg=-Wl,--threads=4')
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
(H/(name+'-inputs.json')).write_text(json.dumps(dict(reservations=caps,source_revision=(H/'revision.txt').read_text().strip(),source_hashes={str(p.relative_to(H/'src')):hashlib.sha256(p.read_bytes()).hexdigest() for p in (H/'src/crates/aspis-prover/src').glob('*.rs')}),indent=2)+'\n')
cmd=['cargo','kani','--no-assertion-reach-checks','-j','4','-p','aspis-prover','--lib','--features','r0','--exact','--harness',target,'-Z','function-contracts','-Z','stubbing','-Z','unstable-options','--output-format','terse','--cbmc-args','--unwinding-assertions']
sys.exit(subprocess.run(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'harness/capped.py'),str(H/'receipts'/name),'Kani compilation then bounded relational byte-oracle comparison; no dense arithmetic; 600 second timeout','--','timeout','600',*cmd]).returncode)
