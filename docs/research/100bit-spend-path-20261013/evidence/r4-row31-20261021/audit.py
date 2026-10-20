#!/usr/bin/env python3
"""Audit focused receipts and exact endpoint-premise removal without Lean."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = 'be9b1f654'
MODULES = ['QueryScanRow31Invariant', 'QueryScanRow31SourcePlacement',
           'R1FinalSoundnessBinPerQueryRow31']
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def statement(name):
    code = (PACKET / 'lean' / (name + '.lean')).read_text()
    return code[code.index('theorem final_soundness'):code.index(' := by', code.index('theorem final_soundness'))]

manifest = json.loads((HERE / 'manifest.json').read_text())
assert len(manifest['attempts']) == 3
accepted = []
for module in MODULES:
    attempts = [a for a in manifest['attempts'] if a['module'] == module]
    assert len(attempts) == 1
    a = attempts[0]
    folder = HERE / (module + '-' + str(a['attempt']))
    source = PACKET / 'lean' / (module + '.lean')
    code = source.read_text()
    assert a['exit'] == 0 and a['swaps'] == 0
    assert a['source_sha256'] == sha(source) == sha(folder / 'source.lean.txt')
    assert json.loads((folder / 'receipt.json').read_text()) == a
    for dep in a['direct_imports']:
        assert dep['sha256'] == sha(dep['path'])
    assert a['deps_fingerprint'] == hashlib.sha256(
        json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest()
    obj = Path('/tmp/codex-cx-r4-row31-20261021-objects') / (module + '.olean')
    assert a['object_sha256'] == sha(obj) and a['object_size'] == obj.stat().st_size
    declarations = re.findall(r'^theorem (\w+)', code, re.M)
    prints = re.findall(r'^#print axioms (\w+)', code, re.M)
    assert declarations == prints
    assert len(a['axioms']) == len(prints)
    for name, report in zip(prints, a['axioms']):
        assert module + '.' + name + "'" in report
        if 'depends on axioms:' in report:
            names = set(re.findall(r'[\w.]+', report.split('[', 1)[1]))
            assert names <= ALLOWED
        else:
            assert 'does not depend on any axioms' in report
    stripped = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', stripped)
    for field in ['argv', 'lean_path', 'source_revision', 'wall_seconds',
                  'peak_rss_bytes', 'swaps', 'exit', 'deps_fingerprint', 'axioms']:
        assert field in a
    accepted.append({k: a[k] for k in ['module', 'attempt', 'exit', 'wall_seconds',
        'peak_rss_bytes', 'swaps', 'source_revision', 'source_sha256', 'axioms']})

before = statement('R1FinalSoundnessBinPerQuery')
after = statement('R1FinalSoundnessBinPerQueryRow31')
start = before.index('    /- R4 row31:')
end = before.index('    /- R13:', start)
assert after == before[:start] + before[end:]
report = (PACKET / 'design/R4-ROW31-20261021.md').read_text()
assert before in report and after in report
assert 'h_R4_row31' not in after
source_map = json.loads((HERE / 'source-map.json').read_text())
for item in source_map['files']:
    assert sha(ROOT / item['path']) == item.get('sha256', item.get('current_sha256'))
    if 'frozen_sha256' in item:
        frozen = subprocess.check_output(['git', 'show', 'b2727acd3:' + item['path']], cwd=ROOT)
        assert hashlib.sha256(frozen).hexdigest() == item['frozen_sha256']
        assert item['identical_to_frozen']
# Files present at base must be unchanged; only additions are authorized.
changes = subprocess.check_output(['git', 'diff', BASE, '--name-status'], cwd=ROOT, text=True)
assert all(line.startswith('A\t') for line in changes.splitlines()), changes
result = {
    'base': BASE,
    'audit_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'status': 'PASS',
    'scope': 'Focused cached-object proof evidence; no coherent frozen release replay',
    'existing_tracked_files_unchanged': True,
    'endpoint_only_removes_h_R4_row31': True,
    'new_or_replacement_endpoint_premises': [],
    'frozen_scanner_and_callers_unchanged': True,
    'standard_axioms_only': True,
    'theorem_audits': sum(len(a['axioms']) for a in accepted),
    'accepted': accepted,
}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'accepted'}, indent=2))
