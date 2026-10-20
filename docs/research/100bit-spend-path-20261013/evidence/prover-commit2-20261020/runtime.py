#!/usr/bin/env python3
import os,subprocess,json
from pathlib import Path
R=Path('/home/dombarker/project-offloads/codex-cx-prover-commit2-20261020')
os.chdir(R/'src')
os.environ.update(PATH='/home/dombarker/.cargo/bin:'+os.environ['PATH'],CARGO_TARGET_DIR=str(R/'runtime-target'),CARGO_BUILD_JOBS='4',CARGO_NET_OFFLINE='true',RUSTFLAGS='-C link-arg=-Wl,--threads=4')
def run(name,args):
    caps=[]
    for p in Path('/sys/fs/cgroup').rglob('memory.max'):
        try:
            v=p.read_text().strip()
            if v!='max' and (p.parent/'cgroup.procs').read_text().strip():caps.append({'path':str(p.parent),'bytes':int(v)})
        except OSError:pass
    (R/(name+'-reservation.json')).write_text(json.dumps(caps,indent=2)+'\n')
    if sum(c['bytes'] for c in caps)+8*2**30>55*2**30:raise SystemExit('reservation hold')
    c=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/name),'Optimized compilation followed by named fixture proof generation / verification; no dense elimination','--',*args]
    subprocess.run(c,check=True)
(R/'src/crates/aspis-r1-cost-probe/src/prover.rs').write_bytes((R/'baseline-prover.rs').read_bytes())
run('baseline-fixture',['cargo','run','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','prover','--example','masked_fixture_gate','--',str(R/'baseline-fixtures')])
(R/'src/crates/aspis-r1-cost-probe/src/prover.rs').write_bytes((R/'carried-prover.rs').read_bytes())
run('carried-fixture',['cargo','run','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','prover','--example','masked_fixture_gate','--',str(R/'carried-fixtures')])
rows=[]
import hashlib
for p in sorted((R/'baseline-fixtures').rglob('proof.bin')):
    q=R/'carried-fixtures'/p.relative_to(R/'baseline-fixtures')
    assert p.read_bytes()==q.read_bytes(),str(p)
    rows.append({'fixture':str(p.relative_to(R/'baseline-fixtures')),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'byte_identical':True})
(R/'byte-identity.json').write_text(json.dumps(rows,indent=2)+'\n')
run('carried-lib',['cargo','test','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--lib','--','--test-threads=1'])
run('carried-retry',['cargo','run','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--example','r1p_retry_gate','--','8',str(R/'retry-ledger'),str(R/'retry.json')])
run('carried-sim',['cargo','run','--release','--locked','--offline','-j','4','-p','aspis-r1-cost-probe','--features','r1p-check','--example','r1p_sim_gate','--',str(R/'sim.json')])
