#!/usr/bin/env python3
"""Collect only named source/JSON/text evidence; never copy build output."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys
R = Path(__file__).resolve().parents[2]
E = R / 'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021'
O = E / sys.argv[1]
O.mkdir()
HOST = 'dombarker@100.108.41.90'
BASE = '/home/dombarker/project-offloads/s126-real-sdk-20261021/'
MAX = 32 * 2**20
count = 0
# No remote arbitrary directory walk. A fixed list created by our own runner.
names = ['admission-before-scope.json', 'launch.json', 'outer-terminal.json',
         'compile-admission.json', 'compile-input.json', 'compile-receipt.json',
         'compile-stdout.log', 'compile-stderr.log', 'compile-time.log',
         'verify-admission.json', 'verify-input.json', 'verify-receipt.json',
         'verify-stdout.log', 'verify-stderr.log', 'verify-time.log', 'terminal.json', 'loops.txt', 'compile-reuse.json']
for version, cases in [('v1', ['positive']), ('v2', ['positive']), ('v3', ['positive']), ('v4', ['positive']), ('v5', ['positive', 'negative']), ('v6', ['negative'])]:
    for case in cases:
        prefix = BASE + 'native-getter-20261026-' + version + '/run-' + case
        for name in names:
            remote = prefix + '/' + name
            code = ('from pathlib import Path; import sys; p=Path(' + repr(remote) + '); '
                    'sys.stdout.buffer.write(p.read_bytes()) if p.is_file() else sys.exit(44)')
            # The Python code is shell-quoted; no contents enter shell code.
            import shlex
            q = subprocess.run(['ssh', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=10',
                                HOST, 'python3 -I -S -B -c ' + shlex.quote(code)], capture_output=True)
            if q.returncode == 44:
                continue
            assert q.returncode == 0, q.stderr.decode()
            count += len(q.stdout)
            assert count < MAX
            dest = O / version / case / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(q.stdout)
for version, local in [('v1', '/private/tmp/s126-native-getter-20261026-v2'),
                       ('v2', '/private/tmp/s126-native-getter-run-20261026-v2'),
                       ('v3', '/private/tmp/s126-native-getter-20261026-v3'),
                       ('v4', '/private/tmp/s126-native-getter-20261026-v4'),
                       ('v5', '/private/tmp/s126-native-getter-20261026-v5'),
                       ('v6', '/private/tmp/s126-native-getter-run-20261026-v6')]:
    directory = Path(local)
    for name in ['binding.json', 'plan.json', 'nuc.py']:
        p = directory / name
        if p.is_file():
            dest = O / version / name
            dest.parent.mkdir(parents=True, exist_ok=True)
            dest.write_bytes(p.read_bytes())
# The native sources are reproducible via the pinned Git revision. Retain
# exact changed source files (with safe Arbitrary derives) and fixture bodies.
w = Path('/private/tmp/s126-native-getter-20261026-v5')
binding = json.loads((w / 'binding.json').read_text())
for name in [*binding['proof_only_arbitrary_derives'], 'harness/src/lib.rs',
             'harness/Cargo.toml', 'Cargo.toml', *binding['manifest_changes']]:
    dest = O / 'source' / name
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes((w / name).read_bytes())
for p in Path(__file__).parent.glob('*'):
    if p.is_file() and p.suffix in ['.py', '.rs']:
        dest = O / 'tools' / p.name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(p.read_bytes())
pins = {str(p.relative_to(O)): hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(O.rglob('*')) if p.is_file()}
(O / 'packet-pins.json').write_text(json.dumps({'schema': 'focused-extractor-proof-packet-v1',
    'files': pins, 'source_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'],cwd=R,text=True).strip(),
    'binary_files_included': False}, indent=2) + '\n')
print(json.dumps({'packet': str(O.relative_to(R)), 'files': len(pins), 'terminal_text_bytes': count}))
