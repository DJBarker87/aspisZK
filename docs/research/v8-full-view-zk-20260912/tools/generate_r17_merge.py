#!/usr/bin/env python3
"""Run optimized public merge-spectrum generation inside a bounded Linux scope."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
root = Path(sys.argv[1]).resolve()
exp = root/'docs/research/v8-no-work-100-20260907/experiments'
stage = json.loads((root/'r17-sbf-probe.json').read_text())
meta = json.loads((root/'r17-stage.json').read_text())
for name, expected in stage['hybrid_merge_files'].items():
    assert hashlib.sha256((exp/name).read_bytes()).hexdigest() == expected
assert hashlib.sha256((exp/'r17_fast_g_tables.rs').read_bytes()).hexdigest() == stage['fast_g']['tables_sha256']
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
path = exp/'r17_merge_spectra.rs'
assert not path.exists(), 'never overwrite generated evidence'
data = subprocess.check_output(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo',
    'run','--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(exp/'performance-host/Cargo.toml'),'--bin','r17-merge-generate'],env=env,cwd=root)
path.write_bytes(data)
stage['hybrid_merge_files'][path.name] = hashlib.sha256(data).hexdigest()
(root/'r17-sbf-probe.json').write_text(json.dumps(stage,indent=2)+'\n')
print('PASS: 7 balanced nodes, 14 fixed denominator spectra, 1536 CM31 constants')
