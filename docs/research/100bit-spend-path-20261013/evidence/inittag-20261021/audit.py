#!/usr/bin/env python3
"""Audit focused receipts and exact single-binder signature weakening; no Lean rerun."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = 'f10ec781f'

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def statement(module):
    text = (PACKET / 'lean' / (module + '.lean')).read_text()
    return 'theorem final_soundness' + text.split('theorem final_soundness', 1)[1].split(' := by', 1)[0] + '\n'

before = statement('R1FinalSoundnessBinPerQueryNoColl')
after = statement('R1FinalSoundnessBinPerQueryTag')
old = '(h_Rwire_tag : BoundaryEvidence s → RWireCompletion.InitialTag D d P (Q + 1161))'
new = '(h_Rwire_tag : BoundaryEvidence s → InitialTagDecision.CheckedRejects D d P (Q + 1161))'
assert before.count(old) == 1
assert after == before.replace(old, new)
(HERE / 'before-statement.lean.txt').write_text(before)
(HERE / 'after-statement.lean.txt').write_text(after)
sigdiff = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
    fromfile='NoColl.final_soundness', tofile='Tag.final_soundness'))
(HERE / 'signature.diff').write_text(sigdiff)
design = (PACKET / 'design/INITTAG-20261021.md').read_text()
assert '```lean\n' + before + '```' in design
assert '```lean\n' + after + '```' in design
assert '```diff\n' + sigdiff + '```' in design

manifest = json.loads((HERE / 'manifest.json').read_text())
final = {a['module']: a for a in manifest['attempts'] if a['final_current']}
assert set(final) == {'InitialTagDecision', 'R1FinalSoundnessBinPerQueryTag'}
reports = 0
for a in manifest['attempts']:
    d = HERE / (a['module'] + '-' + str(a['attempt']))
    for key in ['argv', 'source_revision', 'source_sha256', 'deps_fingerprint', 'exit',
                'wall_seconds', 'peak_rss_bytes', 'swaps', 'axioms', 'errors']:
        assert key in a
    assert sha(d / 'source.lean.txt') == a['source_sha256']
    assert json.loads((d / 'receipt.json').read_text()) == a
    assert hashlib.sha256(json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest() == a['deps_fingerprint']
    assert '-M4400' in a['argv'] and '-j1' in a['argv'] and '-DElab.async=false' in a['argv']
    assert a['swaps'] == 0
    if not a['final_current']:
        continue
    assert a['exit'] == 0 and not a['errors']
    source = PACKET / 'lean' / (a['module'] + '.lean')
    assert sha(source) == a['source_sha256']
    text = source.read_text()
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', text)
    theorems = re.findall(r'^theorem (\w+)', text, re.M)
    assert len(theorems) == len(a['axioms'])
    for theorem in theorems:
        assert '#print axioms ' + theorem in text
        line = next(x for x in a['axioms'] if "." + theorem + "'" in x)
        if 'depends on axioms:' in line:
            names = re.search(r'\[([^]]*)\]', line)[1]
            assert set(x.strip() for x in names.split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}
    reports += len(a['axioms'])
    for imp in a['direct_imports']:
        assert sha(imp['path']) == imp['sha256']
    obj = Path(a['argv'][a['argv'].index('-o') + 1])
    assert sha(obj) == a['object_sha256'] and obj.stat().st_size == a['object_size']

changed = subprocess.check_output(['git', 'diff', '--name-status', BASE], cwd=ROOT, text=True)
for row in changed.splitlines():
    status, path = row.split('\t', 1)
    assert status == 'A', row
    assert path.startswith(str(PACKET.relative_to(ROOT)) + '/'), row
    assert '/lean-candidates/' not in path

result = {'status': 'passed', 'base': BASE, 'signature_change': 'one strictly weaker binder replacement',
          'old_implies_new': 'InitialTagDecision.checked_of_initialTag',
          'strictness': 'InitialTagDecision.checked_strictly_weaker',
          'global_obstruction': 'InitialTagDecision.global_not_implied',
          'attempts': len(manifest['attempts']), 'successful_modules': len(final),
          'axiom_reports': reports, 'swaps': 0,
          'max_attempt_rss_bytes': max(a['peak_rss_bytes'] for a in manifest['attempts']),
          'scope': 'focused cached imports; not a coherent frozen release replay'}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
