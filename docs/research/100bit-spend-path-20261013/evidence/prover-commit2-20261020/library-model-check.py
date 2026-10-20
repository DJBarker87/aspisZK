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
    if sum(c['bytes'] for c in caps)+2*2**30>55*2**30:raise SystemExit('reservation hold')
    c=['systemd-run','--user','--scope','-p','MemoryHigh=1G','-p','MemoryMax=2G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(R/'harness/capped.py'),str(R/'receipts'/name),'Optimized compilation then 65792 live-payload identity cases and Result::map checks; no field elimination or proof generation','--',*args]
    subprocess.run(c,check=True)
os.chdir(R/'library-model-check')
os.environ['CARGO_TARGET_DIR']=str(R/'model-target')
run('library-model-check',['cargo','run','--release','--offline','-j','4','--manifest-path',str(R/'library-model-check/Cargo.toml')])
