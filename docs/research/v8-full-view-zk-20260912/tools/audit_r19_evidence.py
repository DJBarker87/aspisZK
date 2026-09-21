#!/usr/bin/env python3
"""Read-only focused audit of R19's recorded results, not a build rerun."""
import ast
import hashlib
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
repo = root.parents[2]
pins = json.loads((root/'r19-pack/SOURCE_PINS.json').read_text())
for name, expected in pins['git_blob_metadata_from_inspected_sources'].items():
    data = (repo/name).read_bytes()
    actual = hashlib.sha1(f'blob {len(data)}\0'.encode() + data).hexdigest()
    assert actual == expected, (name, actual, expected)
payload = json.loads((root/'r19-pack/MANIFEST.json').read_text())
for name, expected in payload['files'].items():
    data = (root/'r19-pack'/name).read_bytes()
    assert len(data) == expected['bytes'] and hashlib.sha256(data).hexdigest() == expected['sha256'], name
for path in root.joinpath('tools').glob('*r19*.py'):
    ast.parse(path.read_text(), filename=str(path))
for path in root.joinpath('evidence').glob('r19-*/*.json'):
    try:
        json.loads(path.read_text())
    except ValueError as error:
        raise ValueError(f'{path}: {error}') from error

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

leaf = root/'lean/AspisV8R19/ChannelFold.lean'
assert sha(leaf) == '187ab21a2a0f8fdc4bad90a5d681802b8213f07d5c933de7d1b852ae499bc8bb'
ordinary = json.loads((root/'evidence/r19-channel-ordinary-check-a/result.json').read_text())
assert sha(root/'tools/r19_channel_ordinary_check.rs') == ordinary['checker_sha256']
assert ordinary['exit_status'] == 0 and ordinary['channel_terminal_cases'] == 48

for name, totals in [('r19-opening-b', [3906502, 3908034]), ('r19-channel-c', [3304133, 3305430]),
                     ('r19-canonical-a', [3279621, 3280813]), ('r19-queries-a', [3809794, 3811297]),
                     ('r19-combined-20260921-a', [3780805, 3782305])]:
    for world, expected in enumerate(totals):
        path = root/f'evidence/{name}/primary-world{world}.jsonl'
        if name == 'r19-canonical-a':
            suffix = '0' if world == 0 else '1-resumed'
            path = root/f'evidence/{name}/aspis-r19-canonical-host-world{suffix}-a.log'
        elif name == 'r19-queries-a':
            path = root/f'evidence/{name}/svm-world{world}/svm.log'
        elif name == 'r19-combined-20260921-a':
            path = root/f'evidence/{name}/world{world}{"-correct" if world == 0 else ""}.log'
        entries = [json.loads(s) for s in path.read_text().splitlines() if s.startswith('{"accepted"')]
        assert len(entries) == 6
        honest = [e for e in entries if e['case'] == 'honest' and e['accepted']]
        assert len(honest) == 1 and honest[0]['cu'] == expected and honest[0]['cu_limit'] == 100000000
        for e in entries:
            assert e['unchanged_accounts']
            if e['cu_limit'] <= 1400000:
                assert not e['accepted'] and 'ProgramFailedToComplete' in e['error']
        negative = [e for e in entries if e['case'] != 'honest' and e['cu_limit'] == 100000000]
        assert len(negative) == 1 and not negative[0]['accepted'] and 'Custom(6)' in negative[0]['error']

controls = json.loads((root/'evidence/r19-channel-c/results.json').read_text())
assert len(controls['cases']) == 3283 and all(c['exit'] == 0 for c in controls['cases'])
assert sum(c['case'].startswith('noncanonical-') for c in controls['cases']) == 2796
assert sum(c['case'].startswith('old-profile-') for c in controls['cases']) == 2
print('PASS R19 10 source blob pins, 26 packet files, syntax, JSON, Lean/checker hashes, raw CU totals, rejection/resource distinctions and 3283 wire receipts')
