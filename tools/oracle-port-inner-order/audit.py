#!/usr/bin/env python3
"""Read-only receipt, source-pin, axiom and additive-scope audit."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET / 'evidence/inner-order-draft-20261021'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


pins = json.loads((EVIDENCE / 'frozen-sources.json').read_text())
for item in pins['sources']:
    path = ROOT / item['path']
    assert path.stat().st_size == item['size'], item['path']
    assert sha(path) == item['sha256'], item['path']
    if item['role'] == 'unchanged reference':
        old = subprocess.check_output(['git', 'show', pins['base'] + ':' + item['path']], cwd=ROOT)
        assert hashlib.sha256(old).hexdigest() == item['sha256']

changes = subprocess.check_output(['git', 'diff', '--name-status', pins['base']], cwd=ROOT, text=True)
for row in changes.splitlines():
    status, path = row.split('\t')
    assert status == 'A', 'Existing file changed: ' + row
    assert '/lean-candidates/' not in path
    if path.endswith('.lean'):
        assert '/lean/OraclePortInnerOrder' in path

manifest = json.loads((EVIDENCE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
current = {}
for attempt in manifest['attempts']:
    folder = EVIDENCE / (attempt['module'] + '-' + str(attempt['attempt']))
    assert sha(folder / 'source.lean.txt') == attempt['source_sha256']
    assert json.loads((folder / 'receipt.json').read_text()) == attempt
    for field in ['argv', 'source_revision', 'deps_fingerprint', 'exit', 'wall_seconds',
                  'peak_rss_bytes', 'swaps', 'axioms', 'errors']:
        assert field in attempt
    assert attempt['swaps'] == 0
    log = (folder / 'lean.log').read_text()
    assert attempt['axioms'] == re.findall(
        r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    assert str(ROOT / attempt['log']) == str(folder / 'lean.log')
    if attempt['exit'] == 0:
        assert not attempt['errors']
        for line in attempt['axioms']:
            match = re.search(r'\[([\s\S]*?)\]', line)
            assert not match or set(re.split(r',\s*', match[1].strip())) <= allowed
    if attempt['final_current']:
        assert attempt['exit'] == 0
        source = PACKET / 'lean' / (attempt['module'] + '.lean')
        assert sha(source) == attempt['source_sha256']
        body = source.read_text()
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)', body, re.M)
        for theorem in re.findall(r'^theorem\s+(\w+)', body, re.M):
            assert '#print axioms ' + theorem in body, theorem
            assert any("." + theorem + "'" in report for report in attempt['axioms']), theorem
        current[attempt['module']] = attempt

assert set(current) == {Path(i['path']).stem for i in pins['sources'] if i['role'] == 'new Lean source'}
assert 'OraclePortInnerOrderFreeze' in current
print(json.dumps({
    'status': 'pass', 'attempts': len(manifest['attempts']),
    'successful_attempts': sum(a['exit'] == 0 for a in manifest['attempts']),
    'current_modules': len(current),
    'current_theorems': sum(len(re.findall(r'^theorem\s+', (PACKET / 'lean' / (m+'.lean')).read_text(), re.M)) for m in current),
    'accepted_axiom_reports': sum(len(a['axioms']) for a in manifest['attempts'] if a['exit'] == 0),
    'peak_rss_bytes': max(a['peak_rss_bytes'] for a in manifest['attempts']),
    'swaps': 0,
    'scope': 'focused model/counterexample only; no headline or universal verifier budget'
}, indent=2))
