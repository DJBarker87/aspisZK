#!/usr/bin/env python3
"""Retained canonical/gamma controls plus actual v2 proof, optimized and capped by caller."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
root,fixture=map(lambda x:Path(x).resolve(),sys.argv[1:])
exp=root/'docs/research/v8-no-work-100-20260907/experiments'
pins=json.loads((root/'r17-compact-control.json').read_text())
for name,expected in pins['files'].items():
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest()==expected
meta=json.loads((root/'r17-stage.json').read_text())
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
subprocess.run(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo','run',
    '--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(exp/'performance-host/Cargo.toml'),'--bin','aspis-v8-performance-host',
    '--','--gamma-controls'],env=env,cwd=root,check=True)
subprocess.run([sys.executable,str(Path(__file__).with_name('check_r17_host_proof.py')),str(root),str(fixture)],check=True)
