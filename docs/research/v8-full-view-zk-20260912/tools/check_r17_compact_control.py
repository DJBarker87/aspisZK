#!/usr/bin/env python3
"""Run only the new optimized compact-transport control in a caller-owned scope."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
root=Path(sys.argv[1]).resolve()
exp=root/'docs/research/v8-no-work-100-20260907/experiments'
pins=json.loads((root/'r17-compact-control.json').read_text())
for name,expected in pins['files'].items():
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest()==expected
for name,expected in pins.get('core_files',{}).items():
    assert hashlib.sha256((root/name).read_bytes()).hexdigest()==expected
source=(exp/'structured_weights.rs').read_text()
assert (exp/'r17_reused_block_terminal.rs').read_text()==source[
    source.index('fn block_terminal('):source.index('\nfn basis(')]+'\n'
meta=json.loads((root/'r17-stage.json').read_text())
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
subprocess.run(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo',
    'run','--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(exp/'performance-host/Cargo.toml'),
    '--bin',pins.get('bin','r17-compact-transport-check')],env=env,cwd=root,check=True)
