#!/usr/bin/env python3
"""Verify retained evidence hashes and final source/object/axiom pins; no Lean run."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

base = Path(__file__).resolve().parent
root = base.parents[4]
sha = lambda data: hashlib.sha256(data).hexdigest()
manifest = json.loads((base / 'manifest.json').read_text())
for path, expected in manifest['files'].items():
    assert sha((base / path).read_bytes()) == expected, path
with tarfile.open(base / manifest['object_archive']['path'], 'r:gz') as archive:
    object_hashes = {
        member.name: sha(archive.extractfile(member).read())
        for member in archive.getmembers() if member.isfile()
    }
assert object_hashes == manifest['object_archive']['members']
for attempt in manifest['host_attempt_history']:
    receipt_path = base / attempt['receipt']
    receipt = json.loads(receipt_path.read_text())
    assert sha(receipt_path.with_name('source.lean').read_bytes()) == receipt['source_sha256']
    assert sha((base / attempt['runner']).read_bytes()) == receipt['runner_sha256']
    assert sha((base / attempt['input_manifest']).read_bytes()) == receipt['input_manifest_sha256']
axiom_count = 0
for accepted in manifest['accepted_attempts']:
    receipt_path = base / accepted['receipt']
    receipt = json.loads(receipt_path.read_text())
    assert receipt['exit_status'] == 0
    assert sha((root / accepted['source']).read_bytes()) == receipt['source_sha256']
    assert object_hashes[accepted['target'] + '.olean'] == receipt['olean_sha256']
    log = receipt_path.with_name('lean.log').read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log, re.S)
    axioms = {name: [x.strip() for x in values.split(',')] for name, values in reports}
    assert axioms == accepted['axioms']
    assert all(set(values) <= {'propext', 'Classical.choice', 'Quot.sound'} for values in axioms.values())
    assert 'sorryAx' not in log
    axiom_count += len(axioms)
assert len(manifest['accepted_attempts']) == 3 and axiom_count == 9
print('PASS: 3 accepted targets, 9 standard-only axioms audits, all retained pins match.')
