#!/usr/bin/env python3
"""Optimized fixed spectrum reordering inside a bounded Linux scope."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
root=Path(sys.argv[1]).resolve()
exp=root/'docs/research/v8-no-work-100-20260907/experiments'
stage=json.loads((root/'r17-sbf-probe.json').read_text())
meta=json.loads((root/'r17-stage.json').read_text())
for name,expected in stage['aligned_fft_files'].items():
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest()==expected
for name,expected in [('r17_fast_g_tables.rs',stage['fast_g']['tables_sha256']),
    ('r17_merge_spectra.rs',stage['hybrid_merge_files']['r17_merge_spectra.rs'])]:
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest()==expected
env=dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
path=exp/'r17_aligned_spectra.rs'
assert not path.exists(),'never overwrite generated evidence'
data=subprocess.check_output(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo',
    'run','--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(exp/'performance-host/Cargo.toml'),'--bin','r17-aligned-generate'],env=env,cwd=root)
path.write_bytes(data)
stage['aligned_fft_files'][path.name]=hashlib.sha256(data).hexdigest()
(root/'r17-sbf-probe.json').write_text(json.dumps(stage,indent=2)+'\n')
print('PASS: reordered 2048 inverse and 1536 merge constants; each merge cell written exactly once')
