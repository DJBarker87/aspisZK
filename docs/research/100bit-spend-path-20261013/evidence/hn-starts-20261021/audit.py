#!/usr/bin/env python3
"""Check focused source, dependency, receipt and theorem-audit coverage."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = 'e2fbd970b'
OBJECTS = Path('/tmp/codex-cx-hn-starts-20261021-objects')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

manifest = json.loads((HERE / 'manifest.json').read_text())
final = []
new_sources = [PACKET / 'lean' / (name + '.lean') for name in
    sorted({a['module'] for a in manifest['attempts']})]
for source in new_sources:
    name = str(source.relative_to(ROOT))
    assert subprocess.run(['git', 'cat-file', '-e', BASE + ':' + name],
        capture_output=True).returncode, ('existing module changed', name)
for source in new_sources:
    candidates = [a for a in manifest['attempts'] if a['module'] == source.stem]
    assert candidates, ('missing receipt', source)
    current = max(candidates, key=lambda a: a['attempt'])
    assert current['exit'] == 0, current
    assert current['source_sha256'] == sha(source), source
    for a in candidates:
        folder = HERE / (source.stem + '-' + str(a['attempt']))
        assert a['source_sha256'] == sha(folder / 'source.lean.txt')
        assert json.loads((folder / 'receipt.json').read_text())['exit'] == a['exit']
        a['final_current'] = a is current
    for dependency in current['direct_imports']:
        assert sha(dependency['path']) == dependency['sha256'], (source, dependency)
    assert sha(OBJECTS / (source.stem + '.olean')) == current['object_sha256'], source
    assert current['swaps'] == 0
    reports = current['axioms']
    code = source.read_text()
    assert len(reports) == len(re.findall(r'^#print axioms ', code, re.M)), source
    # Every theorem, including private helpers, has its own axiom report.
    declarations = re.findall(r'^(?:private )?theorem (\w+)', code, re.M)
    audited = re.findall(r'^#print axioms (\w+)', code, re.M)
    assert set(declarations) <= set(audited), (source, set(declarations) - set(audited))
    for report in reports:
        if 'depends on axioms:' in report:
            names = set(re.findall(r'\b[A-Za-z_][\w.]*\b', report.split('[', 1)[1]))
            assert names <= ALLOWED, report
    stripped = re.sub(r'/\-.*?\-/', '', code, flags=re.S)
    stripped = re.sub(r'--[^\n]*', '', stripped)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxRecDepth|maxHeartbeats)\b', stripped), source
    final.append({k: current[k] for k in ['module', 'attempt', 'source_sha256', 'exit',
        'wall_seconds', 'peak_rss_bytes', 'swaps', 'object_sha256', 'object_size']})
before = (PACKET / 'lean/R1FinalSoundnessBin.lean').read_text()
after = (PACKET / 'lean/R1FinalSoundnessBinFirstReadBudget.lean').read_text()
for label, text in [('before', before), ('after', after)]:
    begin = text.index('theorem final_soundness')
    end = text.index(' := by', begin)
    assert (HERE / (label + '-statement.lean.txt')).read_text() == text[begin:end] + '\n'
changes = subprocess.check_output(['git', 'diff', BASE, '--name-status'], text=True)
assert all(row.startswith('A\t') for row in changes.splitlines()), changes
manifest['accepted_attempts'] = {a['module']: a['attempt'] for a in final}
manifest['status'] = 'Focused hN counterexample and first-read replacement; original 33-start and 100-bit endpoint not discharged'
(HERE / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
result = {
    'base_revision': BASE,
    'audit_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip(),
    'existing_tracked_files_unchanged': True,
    'source_and_direct_import_hashes_match': True,
    'standard_axioms_only': True,
    'new_modules': len(final),
    'theorem_count': sum(len(re.findall(r'^(?:private )?theorem ', p.read_text(), re.M)) for p in new_sources),
    'accepted_axiom_reports': sum(len(a['axioms']) for a in manifest['attempts'] if a['final_current']),
    'accepted': final,
    'scope': 'Focused cached proof evidence; no coherent frozen release replay or source soundness discharge',
}
(HERE / 'audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'accepted'}, indent=2))
