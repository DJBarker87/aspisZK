#!/usr/bin/env python3
"""Exercise the frozen R19 host verifier; no build and no witness assumptions.

Run in a bounded NUC scope. Reuses one newly created synthetic fixture directory;
original fixtures are read-only. Exit-zero means checked rejection, not a timeout.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess

p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--binary', type=Path, required=True)
p.add_argument('--fixture', type=Path, required=True)
p.add_argument('--old-fixture', type=Path, action='append', default=[])
p.add_argument('--output', type=Path, required=True)
a = p.parse_args()
assert not a.output.exists()
a.output.mkdir()
fixture = a.output / 'synthetic-only'
fixture.mkdir()
for name in ['public.bin', 'transition.bin', 'binding.bin']:
    shutil.copy2(a.fixture / name, fixture / name)
original = (a.fixture / 'proof-1.bin').read_bytes()
assert len(original) <= 40314
env = dict(os.environ, NO_DNA='1')
records = []

def run(name, source, reject=True):
    command = [str(a.binary.resolve()), '--reject-existing' if reject else '--audit-existing', str(source.resolve())]
    r = subprocess.run(command, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=30)
    marker = 'R17_LEGACY_PROFILE_REJECTED' if reject else 'R17_PUBLIC_PREFIX_ACCEPTED'
    assert r.returncode == 0 and marker in r.stdout, (name, r.returncode, r.stdout)
    records.append({'case': name, 'exit': r.returncode, 'checked_rejection': reject})

def changed(name, data):
    (fixture / 'proof-1.bin').write_bytes(data)
    run(name, fixture)

run('honest', a.fixture, False)
for i, old in enumerate(a.old_fixture):
    run(f'old-profile-{i}', old)
# Every limb of the complete new fixed-field region, especially p0 and p2.
for field in range(699):
    for limb in range(4):
        bad = bytearray(original)
        at = 16 * field + 4 * limb
        bad[at:at+4] = ((1 << 31) - 1).to_bytes(4, 'little')
        changed(f'noncanonical-{field}-{limb}', bad)
# Canonical-valued changes must be rejected downstream, not just by parsing.
for field in [358, *range(359, 417), 417, 418, *range(419, 443), *range(443, 699)]:
    bad = bytearray(original)
    at = 16 * field
    value = int.from_bytes(bad[at:at+4], 'little')
    bad[at:at+4] = ((value + 1) % ((1 << 31) - 1)).to_bytes(4, 'little')
    changed(f'canonical-field-change-{field}', bad)
head = 699 * 16 + 52 + 24
for at in [*range(699 * 16, 699 * 16 + 52), *[head + 621*i + off for i in range(22) for off in [0, 403, 589, 620]], len(original)-1]:
    bad = bytearray(original)
    bad[at] ^= 1
    changed(f'authenticated-byte-{at}', bad)
changed('truncated', original[:-1])
changed('extra-trailing-byte', original + b'\0')
result = {'binary_sha256': hashlib.sha256(a.binary.read_bytes()).hexdigest(),
          'proof_sha256': hashlib.sha256(original).hexdigest(),
          'scope': 'host canonical/parser/profile/corruption rejection; not soundness proof',
          'cases': records}
(a.output / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'passed': len(records), 'canonical_positions': 699*4, 'old_profiles': len(a.old_fixture)}))
