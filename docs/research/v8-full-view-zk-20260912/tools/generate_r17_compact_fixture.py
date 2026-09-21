#!/usr/bin/env python3
"""Fresh research-v2 fixture; run under an explicitly capped Linux scope.

Uses the retained optimized prover and BOTH complete verification paths.
Deterministic test entropy and SHA oracle: not a privacy-distribution claim.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
root,output=map(lambda p:Path(p).resolve(),sys.argv[1:])
assert not output.exists()
meta=json.loads((root/'r17-stage.json').read_text())
assert meta['profile']=='AV8/R17/structuredG271-two-channel/compact-binding-research-v2'
env=dict(os.environ)
for key in ['ASPIS_V8_MAX_FRONTIER_SCAN','ASPIS_V8_LIVE_CONTEXT','ASPIS_V8_COMPLETE_CONTEXT','ASPIS_R15_ORACLE_TABLE']:
    env.pop(key,None)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',NO_DNA='1',
    ASPIS_V8_POSITIVE_CASE='honest',ASPIS_R15_SELECTED_SECOND='0',RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
subprocess.run(['/usr/bin/time','-v','/home/dombarker/.cargo/bin/cargo',
    'run','--offline','--locked','--release','--jobs','2','--features',meta['features'],
    '--manifest-path',str(root/'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),
    '--bin','aspis-v8-performance-host','--',str(output)],env=env,cwd=root,check=True)
