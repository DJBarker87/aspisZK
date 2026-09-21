#!/usr/bin/env python3
"""Focused actual-proof host gate in a bounded scope; both verifier paths run."""
import json
import os
from pathlib import Path
import subprocess
import sys
import shutil
import tempfile
root, fixture = map(lambda x: Path(x).resolve(), sys.argv[1:])
meta = json.loads((root / 'r17-stage.json').read_text())
env = dict(os.environ)
env.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin', NO_DNA='1',
    RUSTFLAGS=meta['rustflags'],
    CARGO_TARGET_DIR='/home/dombarker/project-offloads/aspis-v8-performance-20260908.scS2Jz/docs/research/v8-no-work-100-20260907/experiments/performance-host/target')
subprocess.run(['/usr/bin/time', '-v', '/home/dombarker/.cargo/bin/cargo',
    'run', '--offline', '--locked', '--release', '--jobs', '2', '--features', meta['features'],
    '--manifest-path', str(root / 'docs/research/v8-no-work-100-20260907/experiments/performance-host/Cargo.toml'),
    '--bin', 'aspis-v8-performance-host', '--', '--audit-existing', str(fixture)],
    cwd=root, env=env, check=True)
negative = Path(tempfile.mkdtemp(prefix='bad-g-final-', dir=root))
for name in ('public.bin', 'transition.bin', 'binding.bin', 'proof-1.bin'):
    shutil.copyfile(fixture / name, negative / name)
body = bytearray((negative / 'proof-1.bin').read_bytes())
body[697 * 16] ^= 1
(negative / 'proof-1.bin').write_bytes(body)
raise SystemExit(subprocess.run(['/usr/bin/time', '-v',
    str(Path(env['CARGO_TARGET_DIR']) / 'release/aspis-v8-performance-host'),
    '--reject-existing', str(negative)], cwd=root, env=env).returncode)
