#!/usr/bin/env python3
"""Read-only identity of the host's Kani trust boundary; emit hashes, not binaries."""
import hashlib
import json
from pathlib import Path
import subprocess

home = Path('/home/dombarker')
base = home / '.kani/kani-0.67.0/bin'
files = [home/'.cargo/bin/cargo-kani', *[base/n for n in
    ['kani-compiler', 'kani-driver', 'cbmc', 'goto-instrument']]]
result = {'schema': 'multiproof-p6-toolchain-v1', 'files': []}
for path in files:
    target = path.resolve()
    result['files'].append({'path': str(path), 'resolved': str(target),
        'size': target.stat().st_size, 'sha256': hashlib.sha256(target.read_bytes()).hexdigest()})
for name, cmd in [('kani', [str(home/'.cargo/bin/cargo-kani'), 'kani', '--version']),
                  ('cbmc', [str(base/'cbmc'), '--version'])]:
    r = subprocess.run(cmd, capture_output=True, text=True)
    result[name] = {'command': cmd, 'exit': r.returncode, 'stdout': r.stdout, 'stderr': r.stderr}
print(json.dumps(result, indent=2))
