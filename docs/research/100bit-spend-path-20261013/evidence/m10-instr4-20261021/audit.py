#!/usr/bin/env python3
"""Read-only source, object, dependency and theorem-axiom audit; no Lean replay."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

manifest = json.loads((HERE / 'manifest.json').read_text())
checked = []
for r in manifest['attempts']:
    attempt = HERE / (r['module'] + '-' + str(r['attempt']))
    assert sha(attempt / 'source.lean.txt') == r['source_sha256']
    assert json.loads((attempt / 'receipt.json').read_text()) == r
    log = (ROOT / r['log']).read_text()
    assert r['errors'] == (log if r['exit'] else '')
    assert r['swaps'] == 0
for r in manifest['attempts']:
    if not r['final_current']:
        continue
    source = PACKET / 'lean' / (r['module'] + '.lean')
    assert r['exit'] == 0
    assert sha(source) == r['source_sha256']
    obj = Path(r['argv'][r['argv'].index('-o') + 1])
    assert sha(obj) == r['object_sha256']
    assert obj.stat().st_size == r['object_size']
    assert all(sha(i['path']) == i['sha256'] for i in r['direct_imports'])
    fp = hashlib.sha256(json.dumps(r['direct_imports'], sort_keys=True).encode()).hexdigest()
    assert fp == r['deps_fingerprint']
    text = source.read_text()
    assert not re.search(r'\b(sorry|admit|axiom|native_decide|maxHeartbeats|maxRecDepth)\b', text)
    names = re.findall(r'^theorem (\w+)', text, re.M)
    assert len(names) == len(r['axioms']), (r['module'], names, r['axioms'])
    for name, line in zip(names, r['axioms']):
        assert '.' + name + "'" in line
        if 'depends on axioms:' in line:
            axioms = set(re.findall(r'[A-Za-z][A-Za-z.]*', re.search(r'\[([^]]*)\]', line)[1]))
            assert axioms <= {'propext', 'Classical.choice', 'Quot.sound'}
    checked.append({'module': r['module'], 'theorems': names})
changes = subprocess.check_output(['git', 'diff', '--name-status', '12d15d245', '--',
    str(PACKET / 'lean')], cwd=ROOT, text=True)
assert all(row.startswith('A\t') for row in changes.splitlines()), changes
for pin in json.loads((HERE / 'source-pins.json').read_text()):
    p = ROOT / pin['path']
    assert sha(p) == pin['sha256']
    assert p.stat().st_size == pin['size']
    assert subprocess.check_output(['git', 'show',
        pin['published_source_revision'] + ':' + pin['path']], cwd=ROOT) == p.read_bytes()
print(json.dumps({'status': 'pass', 'accepted_targets': checked,
    'theorem_audits': sum(len(r['theorems']) for r in checked),
    'attempts': len(manifest['attempts']),
    'failed_attempts': sum(r['exit'] != 0 for r in manifest['attempts']),
    'max_final_rss_bytes': max(r['peak_rss_bytes'] for r in manifest['attempts'] if r['final_current']),
    'final_wall_seconds': sum(r['wall_seconds'] for r in manifest['attempts'] if r['final_current']),
    'all_attempts_swaps': sum(r['swaps'] for r in manifest['attempts']),
    'release_replay': False,
    'ledger_discharged': False}, indent=2))
