#!/usr/bin/env python3
"""Focused statement helper check, inside a bounded Linux scope only."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tomllib

p=argparse.ArgumentParser()
p.add_argument('--stage',type=Path,required=True)
a=p.parse_args(); root=a.stage.resolve()
meta=json.loads((root/'r18-stage.json').read_text())
for n,h in meta['files'].items():
    assert hashlib.sha256((root/n).read_bytes()).hexdigest()==h,n
host=json.loads((root/'r17-stage.json').read_text())
manifest=root/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'
features=tomllib.loads(manifest.read_text())['features']['selected-v7-kernels']
features=[f.removeprefix('aspis-statement/') for f in features]+['spend-dynamic-rate512','pool-v1-kernel']
env=dict(os.environ,NO_DNA='1',PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',
    RUSTFLAGS=host['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
cmd=['/home/dombarker/.cargo/bin/cargo','test','--manifest-path',str(root/'crates/aspis-statement/Cargo.toml'),
    '--release','--offline','--locked','--jobs','2','--lib','--features',','.join(features),
    'r20_digest_candidate_matches_literal_and_tensor','--','--nocapture','--test-threads=1']
print(json.dumps({'command':cmd,'rustflags':host['rustflags'],'phase':'compilation then 1440 digest helper comparisons; no proof generation'}),flush=True)
raise SystemExit(subprocess.run(['/usr/bin/time','-v']+cmd,cwd=root,env=env).returncode)
