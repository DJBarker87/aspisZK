#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re

ROOT = Path(__file__).resolve().parent
M = json.loads((ROOT / 'manifest.json').read_text())

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def verify(name):
    m = M[name]
    src = ROOT / m['source']
    rec = json.loads((ROOT / m['launch_receipt']).read_text())
    cmd = json.loads((ROOT / m['launch_command']).read_text())
    pre = json.loads((ROOT / m['preflight']).read_text())
    profile = ROOT / m['profile']
    log = (ROOT / m['lean_raw_log']).read_text()
    assert src.is_file() and sha(src) == m['source_sha256'] == rec['source_sha256'] == pre['source_sha256']
    assert rec['object_sha256'] == m['external_object_sha256'] and rec['exit_status'] == 0
    assert rec['source_revision_at_launch'] == m['source_revision_at_launch'] == pre['source_revision']
    assert rec['process_swaps'] == 0 and rec['watchdog_abort'] is None
    assert sha(profile) == pre['profile_sha256']
    assert cmd['argv'][-1].endswith(src.name)
    assert cmd['owner']['target'] == m['module']
    for mod, pin in pre['direct_imports'].items():
        p = Path(pin['path'])
        assert p.is_file() and sha(p) == pin['sha256'], f'direct owner changed: {mod}'
    for decl, axs in m['theorems'].items():
        mt = re.search(re.escape("'" + decl + "' depends on axioms:") + r'([^\n]*(?:\n\s+[^\n]*){0,4})', log)
        assert mt, f'missing #print axioms: {decl}'
        got = mt.group(1)
        assert all(a in got for a in axs), (decl, got)
        assert 'sorryAx' not in got
    if 'closure' in m:
        closure = json.loads((ROOT / m['closure']).read_text())
        assert not closure['missing'] and closure['modules'] == len(closure['owners'])
        for mod, pin in closure['owners'].items():
            p = Path(pin['path'])
            assert p.is_file() and sha(p) == pin['sha256'], f'closure owner changed: {mod}'

for name in ('body_evidence', 'high_array'):
    verify(name)
assert M['body_evidence']['external_object_sha256'] == M['high_array']['depends_on']['S9CandidateBodyEvidenceV1']['sha256']
assert M['body_evidence']['source_sha256'] == '3fc62128c8fa2e99d7eac9ef475b0ee29c7eca2dcc4d545a0111e768dfe40fcd'
assert M['high_array']['source_sha256'] == 'caaf445b3fe25745353242010a3de42f3551760818436da8b418c6ea48b5d60c'
assert not list(ROOT.rglob('*.olean')), 'compiled objects must remain external'
for p in ROOT.rglob('*'):
    if p.is_file():
        assert p.suffix.lower() not in {'.elf', '.so', '.dylib', '.a'}, f'binary included: {p}'
print('PASS: exact source/object pins, receipts, axiom reports, selected closure and source-only packaging')
