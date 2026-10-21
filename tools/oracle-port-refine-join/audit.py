#!/usr/bin/env python3
"""Read-only additive-source and focused-proof receipt audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
HERE = PACKET / 'evidence/refine-join-draft-20261021'
BASE = 'd1ed5eed9'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


pins = json.loads((HERE / 'source-pins.json').read_text())
for path, expected in pins.items():
    assert sha(ROOT / path) == expected, path
changes = subprocess.check_output(['git', 'diff', '--name-status', BASE, '--',
                                  str(PACKET / 'lean')], cwd=ROOT, text=True)
for row in changes.splitlines():
    status, path = row.split('\t')
    assert status == 'A' and Path(path).name.startswith('OraclePortRefineJoin'), row
manifest = json.loads((HERE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
current = {}
for attempt in manifest['attempts']:
    target = HERE / f"{attempt['module']}-{attempt['attempt']}"
    assert sha(target / 'source.lean.txt') == attempt['source_sha256']
    sidecar = json.loads((target / 'receipt.json').read_text())
    assert {k: v for k, v in sidecar.items() if k != 'final_current'} == {
        k: v for k, v in attempt.items() if k != 'final_current'}
    for field in ('argv', 'source_revision', 'source_sha256', 'direct_imports',
                  'deps_fingerprint', 'exit', 'wall_seconds', 'peak_rss_bytes',
                  'swaps', 'axioms', 'errors', 'log', 'time'):
        assert field in attempt, (target, field)
    assert (ROOT / attempt['log']).is_file()
    assert (ROOT / attempt['time']).is_file()
    if attempt['final_current']:
        assert attempt['exit'] == 0 and not attempt['errors'], target
        assert attempt['swaps'] == 0, target
        source = PACKET / 'lean' / (attempt['module'] + '.lean')
        assert sha(source) == attempt['source_sha256'], source
        for report in attempt['axioms']:
            axioms = re.search(r'depends on axioms: \[([\s\S]*?)\]', report)
            if axioms:
                assert {a.strip() for a in axioms[1].split(',')} <= ALLOWED, report
        current[attempt['module']] = attempt
modules = sorted((PACKET / 'lean').glob('OraclePortRefineJoin*.lean'))
count = 0
for source in modules:
    assert source.stem in current, source
    text = source.read_text()
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', text), source
    for theorem in re.findall(r'^theorem (\w+)', text, re.M):
        assert f'#print axioms {theorem}' in text, (source, theorem)
        assert any(re.search(r'\.' + re.escape(theorem) + "'", line)
                   for line in current[source.stem]['axioms']), (source, theorem)
        count += 1
print(json.dumps({'status': 'pass', 'base': BASE, 'modules': len(modules),
                  'new_theorems': count, 'attempts': len(manifest['attempts']),
                  'successful_attempts': sum(a['exit'] == 0 for a in manifest['attempts']),
                  'peak_rss_bytes': max(a['peak_rss_bytes'] for a in manifest['attempts']),
                  'swaps': sum(a['swaps'] for a in manifest['attempts']),
                  'scope': 'focused compatible cached imports; not a frozen release replay'}, indent=2))
