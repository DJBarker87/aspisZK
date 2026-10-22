#!/usr/bin/env python3
"""Host-only, one unchanged retained module per authorized proof attempt."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

module, attempt = sys.argv[1:]
assert re.fullmatch(r'[A-Za-z0-9_.]+', module)
assert 10400 <= int(attempt) <= 10499
W = Path(__file__).resolve().parent
base = Path('/home/dombarker/project-offloads')
J = base / 'aspis-joint-20261019'
env = json.load(open(base / 'r1-privacy-build-integration-20261019/env/J.json'))
manifest = json.load(open(W / 'preflight-expanded.json'))
record = manifest['resolved_sources'][module]
source = W / 'pinned' / record['path']
digest = hashlib.sha256(source.read_bytes()).hexdigest()
assert digest == record['sha256']
dest = J / 'sources' / (module.replace('.', '/') + '.lean')
if dest.exists():
    assert dest.read_bytes() == source.read_bytes(), 'refuse to change retained source'
else:
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(source.read_bytes())
paths = [J / 'objects'] + [Path(p) for p in env['LEAN_PATH'].split(':')]
dependencies = []
for m in record['imports']:
    p = next((r / (m.replace('.', '/') + '.olean') for r in paths
              if (r / (m.replace('.', '/') + '.olean')).is_file()), None)
    assert p is not None, 'missing object: ' + m
    dependencies.append((m, str(p), hashlib.sha256(p.read_bytes()).hexdigest()))
fp = hashlib.sha256(json.dumps(dependencies, sort_keys=True).encode()).hexdigest()
cmd = ['sh', str(W.parent / 'run-joint.sh'), attempt, module.replace('.', '/'), 'J', '7000', '8', fp]
start = time.monotonic()
result = subprocess.run(cmd, text=True, capture_output=True)
evidence = base / 'aspis-fs-generic-20261006/evidence'
receipt = {'module': module, 'attempt': 'J' + attempt, 'source_sha256': digest,
           'revision': (W / 'revision.txt').read_text().strip(), 'deps_fingerprint': fp,
           'dependencies': dependencies, 'command': cmd,
           'controller_exit': result.returncode, 'controller_wall_seconds': time.monotonic() - start,
           'stdout': result.stdout, 'stderr': result.stderr}
for stem in ['out', 'time', 'sha']:
    p = evidence / (stem + '-' + attempt + ('.txt' if stem == 'sha' else '.log'))
    if p.exists():
        receipt[stem] = p.read_text()
(W / ('J' + attempt + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
print(result.stdout, result.stderr, flush=True)
assert re.search(r'^exit=0$', receipt.get('out', ''), re.M), 'retained compile failed'
