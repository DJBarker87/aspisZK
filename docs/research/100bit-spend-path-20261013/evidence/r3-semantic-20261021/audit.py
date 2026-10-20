#!/usr/bin/env python3
"""Audit focused receipts and signature; does not rerun Lean."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
ROOT = PACKET.parents[2]
BASE = '8f219015822503ca790ecdd32dbc889ca7952f8e'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def signature(s, name='final_soundness'):
    marker = 'theorem ' + name + '\n'
    start = s.index(marker)
    s = s[start:s.index(' := by', start)]
    return re.sub(r'\s*/\-.*?\-/', '', s, flags=re.S) + '\n'


manifest = json.loads((HERE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
finals = [a for a in manifest['attempts'] if a['final_current']]
assert len({a['module'] for a in finals}) == len(finals)
modules = sorted(p.stem for p in (PACKET / 'lean').glob('R3*.lean')) + ['R1FinalSoundnessBinPerQueryR3']
# Only this packet's sources are selected below, not unrelated R3 basenames.
modules = sorted({a['module'] for a in manifest['attempts']})
assert {a['module'] for a in finals} == set(modules)
for a in manifest['attempts']:
    attempt = HERE / f"{a['module']}-{a['attempt']}"
    assert sha(attempt / 'source.lean.txt') == a['source_sha256']
    log = (ROOT / a['log']).read_text()
    reports = re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    assert reports == a['axioms']
    assert a['peak_rss_bytes'] > 0 and a['swaps'] >= 0
    assert a['source_revision'] and a['wall_seconds'] > 0
    assert hashlib.sha256(json.dumps(a['direct_imports'], sort_keys=True).encode()).hexdigest() == a['deps_fingerprint']
    if not a['final_current']:
        continue
    assert a['exit'] == 0 and not a['errors']
    src = PACKET / 'lean' / (a['module'] + '.lean')
    assert sha(src) == a['source_sha256']
    obj = Path('/tmp/codex-cx-r3-semantic-20261021-objects') / (a['module'] + '.olean')
    assert sha(obj) == a['object_sha256'] and obj.stat().st_size == a['object_size']
    for dep in a['direct_imports']:
        assert sha(dep['path']) == dep['sha256']
    for report in reports:
        axioms = re.search(r'\[([^]]*)\]', report)
        assert not axioms or set(re.findall(r'[\w.]+', axioms[1])) <= ALLOWED
    theorem_names = re.findall(r'^theorem\s+(\w+)', src.read_text(), re.M)
    printed_names = re.findall(r'^#print axioms\s+(\w+)', src.read_text(), re.M)
    assert sorted(theorem_names) == sorted(printed_names)
    assert len(reports) == len(theorem_names)
    text = re.sub(r'/\-.*?\-/', '', src.read_text(), flags=re.S)
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b', text)

before = signature((PACKET / 'lean/R1FinalSoundnessBinPerQueryR19.lean').read_text())
after = signature((PACKET / 'lean/R1FinalSoundnessBinPerQueryR3.lean').read_text())
assert after == before
alt = signature((PACKET / 'lean/R1FinalSoundnessBinPerQueryR3.lean').read_text(),
                'final_soundness_from_equations').replace('theorem final_soundness_from_equations',
                                                         'theorem final_soundness', 1)
expected = before.replace('h_R3_semantic :', 'h_R3_equations :').replace(
    'HchecksReaderComposition.SemanticEndpoint (source H).decoded',
    'R3SemanticRemainingJoins.EquationEndpoint (source H).decoded')
assert alt == expected
assert (HERE / 'equations-statement.lean.txt').read_text() == alt
assert (HERE / 'equations-signature.diff').read_text() == ''.join(difflib.unified_diff(
    before.splitlines(True), alt.splitlines(True),
    fromfile='R19.final_soundness', tofile='R3.final_soundness_from_equations'))
assert (HERE / 'before-statement.lean.txt').read_text() == before
assert (HERE / 'after-statement.lean.txt').read_text() == after
assert (HERE / 'signature.diff').read_text() == ''.join(difflib.unified_diff(
    before.splitlines(True), after.splitlines(True),
    fromfile='R19.final_soundness', tofile='R3.final_soundness'))
changes = subprocess.check_output(['git', 'diff', '--name-status', BASE, '--'], cwd=ROOT, text=True)
assert all(row.startswith('A\t') for row in changes.splitlines())
assert not subprocess.check_output(['git', 'diff', '--check'], cwd=ROOT, text=True)
summary = {
    'status': 'passed', 'schema': 'focused-extractor-proof-packet-v1',
    'base': BASE, 'audited_revision': subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip(),
    'final_modules': modules, 'attempts': len(manifest['attempts']),
    'accepted_axiom_reports': sum(len(a['axioms']) for a in finals),
    'failed_attempts': sum(a['exit'] != 0 for a in manifest['attempts']),
    'max_final_rss_bytes': max(a['peak_rss_bytes'] for a in finals),
    'final_swaps': sum(a['swaps'] for a in finals),
    'signature_change': 'main unchanged; alternate R3 equation interface equivalent on parser image',
    'release_limit': 'Focused cached checks; no coherent frozen manifest replay or source refinement discharge',
}
(HERE / 'audit.json').write_text(json.dumps(summary, indent=2) + '\n')
print(json.dumps(summary, indent=2))
