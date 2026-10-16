#!/usr/bin/env python3
"""Verify retained failed extraction attempts; makes no proof/success claim."""
from pathlib import Path
import hashlib, json, subprocess, tarfile

base = Path(__file__).resolve().parent
sha = lambda data: hashlib.sha256(data).hexdigest()
archive = base / 'failed-extraction-evidence.tar.gz'
assert sha(archive.read_bytes()) == 'af593c339c67f8434df85c0873f03389e9af4753abccc0bb958df0033e756bd0'
with tarfile.open(archive) as tf:
    files = {m.name: tf.extractfile(m).read() for m in tf if m.isfile()}
assert len(files) == 61
for name, pin in json.loads(files['archive-members.json']).items():
    assert sha(files[name]) == pin['sha256'] and len(files[name]) == pin['bytes'], name
count = 0
for prefix in ['', 'before/', 'indexed/', 'status/']:
    pins = json.loads(files[prefix + 'input/source-pins.json'])
    for name, digest in pins['kit_files'].items():
        data = subprocess.check_output(['git', 'show', pins['source_revision'] + ':' + name], cwd=base)
        assert sha(data) == digest, (prefix, name)
        count += 1
    for name in files:
        if name.startswith(prefix + 'input/') and name != prefix + 'input/source-pins.json':
            rel = name[len(prefix + 'input/'):]
            assert sha(files[name]) == pins['kit_files'][rel], name
receipts = []
for name, data in files.items():
    if not name.endswith('/receipt.json'):
        continue
    r = json.loads(data)
    expected = 2 if '/aeneas-a/' in name else 0
    assert r['exit_status'] == expected, name
    assert r['swaps'] == 0
    assert r['limits'] == {'memory.high': '6442450944', 'memory.max': '8589934592', 'memory.swap.max': '0'}
    receipts.append(name)
assert len(receipts) == 8
for prefix in ['', 'indexed/']:
    assert b'Early returns inside loops' in files[prefix + 'runs/aeneas-a/stdout.log']
assert b'Could not match the contexts' in files['status/runs/aeneas-a/stdout.log']
trace = files['before/runs/trace-a/stdout.log']
assert sha(trace) == '628a3418096f93d769955ff18e7ac2f4e8fcb25b659b66aac3360204ad94efff'
assert trace.endswith(b'complete 20720\n')
print(f'PASS: 61 members, {count} Git source pins, 8 receipts, 3 retained extraction failures; baseline 20,720 cases only')
