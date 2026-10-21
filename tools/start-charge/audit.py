#!/usr/bin/env python3
"""Audit the additive start-charge packet, signatures and accepted receipts."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET / 'evidence/start-charge-20261021'
LEAN = PACKET / 'lean'
MODULES = ['StartChargePrefix', 'StartChargeHit', 'StartChargeCompletion',
           'StartChargeClean', 'StartChargeProbability', 'StartChargeNumeric',
           'OraclePortHeadlineFrozenPerAttempt']
BASE = '2343a4a72'
INTEGRATED = PACKET / 'evidence/port-integrate-20261021'
BASELINE_COMMAND = INTEGRATED / 'OraclePortFrozenOrderHeadline-1/command.json'
EXPECTED_PATH = '/tmp/codex-cx-start-charge-20261021-objects:' + json.loads(BASELINE_COMMAND.read_text())['lean_path']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def signature(module, theorem="final_soundness"):
    text = (LEAN / (module + '.lean')).read_text()
    return text.split('theorem ' + theorem + '\n', 1)[1].split(' :\n', 1)[0] + '\n'

before = signature('OraclePortFrozenOrderHeadline')
after = signature('OraclePortHeadlineFrozenPerAttempt')
(EVIDENCE / 'premises-before.lean.txt').write_text(before)
(EVIDENCE / 'premises-after.lean.txt').write_text(after)
diff = ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                    fromfile='adopted-premises', tofile='per-attempt-premises'))
(EVIDENCE / 'premises.diff').write_text(diff)
assert not diff, 'Endpoint premise signature changed'
old_range = signature('OraclePortFrozenOrderHeadline', 'per_query')
new_range = signature('OraclePortHeadlineFrozenPerAttempt', 'per_query')
(EVIDENCE / 'per-query-premises-before.lean.txt').write_text(old_range)
(EVIDENCE / 'per-query-premises-after.lean.txt').write_text(new_range)
(EVIDENCE / 'per-query-premises.diff').write_text(''.join(difflib.unified_diff(
    old_range.splitlines(True), new_range.splitlines(True), fromfile='adopted', tofile='per-attempt')))
assert old_range.replace('    (hlo : 32 ≤ Q) (hhi : Q ≤ Qmax)', '    (hhi : Q ≤ Qmax)') == new_range

manifest = json.loads((EVIDENCE / 'manifest.json').read_text())
accepted = []
for module in MODULES:
    source = LEAN / (module + '.lean')
    text = source.read_text()
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', text), module
    declarations = re.findall(r'^(?:private )?theorem (\w+)', text, re.M)
    for name in declarations:
        assert '#print axioms ' + name in text, (module, name)
    matches = [a for a in manifest['attempts'] if a['module'] == module and a['exit'] == 0
               and a['source_sha256'] == sha(source) and a['final_current']]
    assert len(matches) == 1, (module, 'missing unique current successful compile')
    attempt = matches[0]
    assert attempt['lean_path'] == EXPECTED_PATH, (module, 'nonfinal environment')
    for imported in attempt['direct_imports']:
        assert sha(Path(imported['path'])) == imported['sha256'], (module, imported['module'])
    assert len(attempt['axioms']) == len(declarations), (module, 'missing axiom reports')
    for line in attempt['axioms']:
        assert 'sorryAx' not in line and ('does not depend on any axioms' in line or (
            'depends on axioms:' in line and set(re.findall(r'\[([^]]*)\]', line)[0]
            .replace('\n','').replace(' ','').split(',')) <= {'propext','Classical.choice','Quot.sound'}))
    accepted.append({k: attempt[k] for k in ['module','attempt','source_sha256','exit',
        'wall_seconds','peak_rss_bytes','swaps','axioms','source_revision','deps_fingerprint']})
changed = subprocess.check_output(['git','diff','--name-only',BASE], cwd=ROOT, text=True).splitlines()
old_lean_changed = [p for p in changed if p.startswith(str(LEAN.relative_to(ROOT)) + '/')
                    and Path(p).stem not in MODULES]
assert not old_lean_changed, old_lean_changed
shipped = [p for p in changed if p.startswith('crates/') or p.endswith('.rs') or p.endswith('Cargo.toml')]
assert not shipped, shipped
integrated_objects = []
for attempt in json.loads((INTEGRATED / 'manifest.json').read_text())['attempts']:
    if attempt['exit'] != 0:
        continue
    obj = Path('/tmp/codex-cx-port-integrate-20261021-objects') / (attempt['module'].replace('.','/') + '.olean')
    assert sha(obj) == attempt['object_sha256'], ('integrated cache changed', attempt['module'])
    src = LEAN / (attempt['module'].replace('.','/') + '.lean')
    assert sha(src) == attempt['source_sha256'], ('integrated source changed', attempt['module'])
    integrated_objects.append({'module': attempt['module'], 'object_sha256': sha(obj),
                               'source_sha256': sha(src)})
result = {'schema': 'start-charge-audit-v1', 'source_revision': subprocess.check_output(
    ['git','rev-parse','HEAD'], cwd=ROOT, text=True).strip(), 'base': BASE,
    'premise_signature_diff_empty': not diff, 'accepted': accepted,
    'integrated_baseline_command_sha256': sha(BASELINE_COMMAND),
    'integrated_reused_objects': integrated_objects,
    'shipped_source_changes': shipped, 'existing_lean_changes': old_lean_changed,
    'scope': 'focused cached-object proof packet; source joins and coherent release replay retained'}
(EVIDENCE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'modules': len(accepted), 'axiom_reports': sum(len(a['axioms']) for a in accepted),
                  'premise_signature_diff_empty': not diff, 'shipped_source_changes': shipped}))
