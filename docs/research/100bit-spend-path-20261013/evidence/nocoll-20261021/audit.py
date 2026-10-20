#!/usr/bin/env python3
"""Check the headline signature changed only by the five promised guards."""
from pathlib import Path
import difflib
import hashlib
import json
import re
import subprocess

here = Path(__file__).resolve().parent
packet = here.parent.parent
lean = packet / 'lean'
old = (lean / 'R1FinalSoundnessBinPerQueryRWire.lean').read_text()
new = (lean / 'R1FinalSoundnessBinPerQueryNoColl.lean').read_text()
names = ['h_R16_instance', 'h_R13', 'h_R14_backend', 'h_R15_writer', 'h_R3_semantic']
guard = '\n      ¬ binaryCollision (Q + 1161) (eval H (recorded D d P)) →'
def statement(s):
    return s[s.index('theorem final_soundness'):s.index(' := by\n', s.index('theorem final_soundness'))]
before, after = statement(old), statement(new)
assert after.count(guard) == 5
assert after.replace(guard, '') == before
(here / 'before-statement.lean.txt').write_text(before + '\n')
(here / 'after-statement.lean.txt').write_text(after + '\n')
(here / 'signature.diff').write_text(''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True), fromfile='RWire', tofile='NoColl')))
rows = []
for name in names:
    def binder(s):
        start = s.index('    (' + name + ' : ')
        return s[start:s.index('\n    /-', start)]
    b, a = binder(old), binder(new)
    assert a.replace(guard, '') == b
    (here / (name + '-before.txt')).write_text(b + '\n')
    (here / (name + '-after.txt')).write_text(a + '\n')
    rows.append({'premise': name, 'only_inserted_text': guard,
                 'before': name + '-before.txt', 'after': name + '-after.txt'})
new_modules = ['NoCollPremiseWeakening', 'NoCollRWireCompletion', 'NoCollCleanModelBin',
               'R1FinalSoundnessBinPerQueryNoColl']
for name in new_modules:
    text = (lean / (name + '.lean')).read_text()
    assert not re.search(r'\b(sorry|admit|native_decide)\b|^axiom\b|set_option\s+(maxRecDepth|maxHeartbeats)', text, re.M)
manifest = json.loads((here / 'manifest.json').read_text())
for row in manifest['attempts']:
    for axioms in re.findall(r'depends on axioms: \[([^\]]*)\]', '\n'.join(row['axioms'])):
        assert set(axioms.replace('\n', '').replace(' ', '').split(',')) <= {'propext', 'Classical.choice', 'Quot.sound'}
checks = []
for name in new_modules:
    source = lean / (name + '.lean')
    current = [a for a in manifest['attempts'] if a['module'] == name and a['final_current']]
    assert len(current) == 1
    row = current[0]
    assert row['exit'] == 0 and row['swaps'] == 0 and not row['errors']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == row['source_sha256']
    assert (here / (name + '-' + str(row['attempt'])) / 'source.lean.txt').read_bytes() == source.read_bytes()
    declarations = re.findall(r'^(?:private )?theorem (\w+)', source.read_text(), re.M)
    prints = re.findall(r'^#print axioms (\w+)', source.read_text(), re.M)
    assert sorted(declarations) == sorted(prints)
    assert len(row['axioms']) == len(prints)
    for obj in row['direct_imports']:
        assert hashlib.sha256(Path(obj['path']).read_bytes()).hexdigest() == obj['sha256']
    checks.append({'module': name, 'attempt': row['attempt'], 'exit': row['exit'],
                   'wall_seconds': row['wall_seconds'], 'peak_rss_bytes': row['peak_rss_bytes'],
                   'swaps': row['swaps'], 'axiom_reports': len(prints),
                   'source_and_direct_import_hashes_match': True})
changed = subprocess.check_output(['git', 'diff', '--name-only', '7dac4fa12', '--', str(lean)], text=True).splitlines()
assert set(Path(p).name for p in changed) == {m + '.lean' for m in new_modules}
for f in changed:
    assert subprocess.run(['git', 'cat-file', '-e', '7dac4fa12:' + f], capture_output=True).returncode != 0
report = {'base_endpoint': 'R1FinalSoundnessBinPerQueryRWire.final_soundness',
          'new_endpoint': 'R1FinalSoundnessBinPerQueryNoColl.final_soundness',
          'only_changes': rows, 'conclusion_verbatim_equal': True,
          'other_premises_verbatim_equal': True,
          'new_source_sha256': {m: hashlib.sha256((lean / (m + '.lean')).read_bytes()).hexdigest() for m in new_modules},
          'standard_axioms_only_in_recorded_attempts': True,
          'compiled_source_revision': manifest.get('final_source_revision') or subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
          'only_new_lean_modules': True, 'focused_checks': checks,
          'total_axiom_reports': sum(c['axiom_reports'] for c in checks)}
(here / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print('Signature audit passed: exactly five guard insertions; unchanged conclusion and all other premises.')
