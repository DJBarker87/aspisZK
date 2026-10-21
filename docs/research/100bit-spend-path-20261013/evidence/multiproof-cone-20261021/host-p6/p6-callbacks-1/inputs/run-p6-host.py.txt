#!/usr/bin/env python3
"""Run only named P6 function roots in the worker's capped host workspace."""
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
name, *selectors = sys.argv[1:]
assert selectors and all(s.startswith(('p6_certificates::', 'proofs::')) for s in selectors)
env = {**os.environ, 'PATH': '/home/dombarker/.cargo/bin:' + os.environ['PATH'],
       'CARGO_BUILD_JOBS': '4', 'CARGO_PROFILE_DEV_OPT_LEVEL': '3',
       'CARGO_PROFILE_DEV_DEBUG': '0', 'CARGO_NET_OFFLINE': 'true',
       'RUSTFLAGS': '-C opt-level=3 -C link-arg=-Wl,--threads=4',
       'MP_EXPECTED': 'optimized Kani compilation, then named function equality; no arithmetic elimination'}
subprocess.run(['python3', str(HERE/'reservation.py'), str(ROOT/('reservation-'+name+'.json'))], check=True)
cmd = ['cargo', 'kani', '--manifest-path', str(HERE/'Cargo.toml'), '--lib', '--exact',
       '--solver', 'cadical', '--output-format', 'old', '--no-assertion-reach-checks',
       '-Z', 'function-contracts', '-Z', 'stubbing', '-Z', 'unstable-options', '--harness-timeout', '240']
for selector in selectors:
    cmd += ['--harness', selector]
cmd += ['--cbmc-args', '--unwinding-assertions']
os.chdir(ROOT)
raise SystemExit(subprocess.call(['systemd-run', '--user', '--scope', '-q',
    '-p', 'MemoryHigh=6G', '-p', 'MemoryMax=8G', '-p', 'MemorySwapMax=0', '-p', 'TasksMax=64',
    'python3', str(HERE/'host-run.py'), name, 'timeout', '900', *cmd], env=env))
