#!/usr/bin/env python3
"""Audit focused receipts without repeating Lean compilation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '2f021de67'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = json.loads((HERE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
finals = []
for a in manifest['attempts']:
    out = HERE / f"{a['module']}-{a['attempt']}"
    assert sha(out / 'source.lean.txt') == a['source_sha256']
    assert json.loads((out / 'receipt.json').read_text()) == a
    command = json.loads((out / 'command.json').read_text())
    for k, v in command.items():
        assert a[k] == v, k
    fp = hashlib.sha256(json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest()
    assert fp == a['deps_fingerprint']
    assert all(x in a['argv'] for x in ['-j1', '-M4400', '-DElab.async=false'])
    assert a['wall_seconds'] > 0 and a['peak_rss_bytes'] > 0 and a['swaps'] >= 0
    assert a['source_revision']
    if not a['final_current']:
        continue
    assert a['exit'] == 0 and not a['errors']
    source = PACKET / 'lean' / (a['module'] + '.lean')
    assert sha(source) == a['source_sha256']
    obj = Path(a['argv'][a['argv'].index('-o') + 1])
    assert sha(obj) == a['object_sha256'] and obj.stat().st_size == a['object_size']
    for dep in a['direct_imports']:
        assert sha(dep['path']) == dep['sha256'], dep['module']
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|native_decide|maxRecDepth|maxHeartbeats)\b', text)
    assert not re.search(r'^\s*axiom\s', text, re.M)
    names = re.findall(r'^theorem\s+(\w+)', text, re.M)
    audits = a['axioms']
    assert len(names) == len(audits), (a['module'], names, audits)
    for name in names:
        assert f'#print axioms {name}' in text
        line = next(x for x in audits if x.startswith(f"'AspisR1.{a['module']}.{name}'"))
        if 'depends on axioms:' in line:
            values = {x.strip() for x in line.split('[', 1)[1].rstrip(']').split(',')}
            assert values <= ALLOWED, line
    finals.append({'module': a['module'], 'attempt': a['attempt'],
                   'theorems': len(names), 'wall_seconds': a['wall_seconds'],
                   'peak_rss_bytes': a['peak_rss_bytes'], 'swaps': a['swaps']})
assert {x['module'] for x in finals} == {
    'R16CanonReduction', 'R16CanonExtractor', 'R16CanonRecorded',
    'R1FinalSoundnessBinPerQueryCanon'}
before = (HERE / 'signature-before.lean.txt').read_bytes()
after = (HERE / 'signature-after.lean.txt').read_bytes()
assert before == after and not (HERE / 'signature.diff').read_bytes()
changes = subprocess.check_output(['git', 'diff', '--name-status', BASE, '--'], cwd=ROOT, text=True)
assert all(row.startswith('A\t') for row in changes.splitlines()), changes
assert all('/r16-canon-20261021/' in row or '/R16-CANON-20261021.md' in row or
           re.search(r'/lean/(R16Canon(Reduction|Extractor|Recorded)|R1FinalSoundnessBinPerQueryCanon)\.lean$', row)
           for row in changes.splitlines()), changes
result = {'status': 'pass', 'base': BASE, 'finals': finals,
          'theorems': sum(x['theorems'] for x in finals),
          'attempts': len(manifest['attempts']), 'signature_changed': False,
          'scope': 'focused additive model packet; no frozen release replay'}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
