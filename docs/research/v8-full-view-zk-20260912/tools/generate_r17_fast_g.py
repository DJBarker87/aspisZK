#!/usr/bin/env python3
"""Optimized fixed-table generation inside a bounded Linux scope."""
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
root = Path(sys.argv[1]).resolve()
exp = root / 'docs/research/v8-no-work-100-20260907/experiments'
stage = json.loads((root / 'r17-sbf-probe.json').read_text())
meta = json.loads((root / 'r17-stage.json').read_text())
assert hashlib.sha256((exp / 'r17_fast_g_generate.rs').read_bytes()).hexdigest() == stage['fast_g']['r17_fast_g_generate.rs']
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', NO_DNA='1', RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
data = subprocess.check_output(['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/cargo',
    'run', '--offline', '--locked', '--release', '--jobs', '2', '--features', meta['features'],
    '--manifest-path', str(exp / 'performance-host/Cargo.toml'), '--bin', 'r17-fast-g-generate'], env=env, cwd=root)
path = exp / 'r17_fast_g_tables.rs'
assert not path.exists(), 'never overwrite previously generated evidence'
path.write_bytes(data)
stage['fast_g']['tables_sha256'] = hashlib.sha256(data).hexdigest()
(root / 'r17-sbf-probe.json').write_text(json.dumps(stage, indent=2) + '\n')
print('PASS: generated fixed product tree, root powers and inverse spectrum with optimized Rust')
