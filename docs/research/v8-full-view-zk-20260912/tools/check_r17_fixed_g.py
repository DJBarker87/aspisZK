#!/usr/bin/env python3
"""Run focused exact-table/weight checks, then both actual host proof paths."""
import json
import os
from pathlib import Path
import subprocess
import sys

root, fixture = map(lambda s: Path(s).resolve(), sys.argv[1:])
meta = json.loads((root / 'r17-stage.json').read_text())
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', NO_DNA='1',
    RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
subprocess.run(['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/cargo',
    'run', '--offline', '--locked', '--release', '--jobs', '2',
    '--features', meta['features'], '--manifest-path',
    str(root / 'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),
    '--bin', 'r17-tensor-check'], env=env, cwd=root, check=True)
subprocess.run([sys.executable, str(Path(__file__).with_name('check_r17_host_proof.py')),
    str(root), str(fixture)], check=True)
