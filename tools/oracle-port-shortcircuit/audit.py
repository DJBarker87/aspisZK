#!/usr/bin/env python3
"""Read-only verification of the additive focused packet; runs no compiler."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]
PACKET = ROOT / 'docs/research/100bit-spend-path-20261013'
EVIDENCE = PACKET / 'evidence/shortcircuit-draft-20261021'


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def signature(module):
    text = (PACKET / 'lean' / module).read_text()
    start = text.index('theorem final_soundness\n')
    return text[start:text.index(':=', start)].rstrip() + '\n'


manifest = json.loads((EVIDENCE / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
final = {}
for attempt in manifest['attempts']:
    folder = EVIDENCE / f"{attempt['module']}-{attempt['attempt']}"
    assert json.loads((folder / 'receipt.json').read_text()) == attempt
    assert sha(folder / 'source.lean.txt') == attempt['source_sha256']
    command = json.loads((folder / 'command.json').read_text())
    for key in command:
        assert command[key] == attempt[key], key
    assert attempt['argv'][1:4] == ['-j1', '-M4400', '-DElab.async=false']
    assert attempt['argv'][7].startswith('/tmp/codex-cx-shortcircuit-draft-20261021-objects/')
    fingerprint = {'imports': attempt['direct_imports'], 'lean_path': attempt['lean_path'],
                   'environment_artifacts': attempt['environment_artifacts']}
    assert hashlib.sha256(json.dumps(fingerprint, sort_keys=True).encode()).hexdigest() == attempt['deps_fingerprint']
    for imp in attempt['direct_imports']:
        assert sha(imp['path']) == imp['sha256'], imp['module']
    log = (folder / 'lean.log').read_text()
    timing = (folder / 'time.log').read_text()
    assert int(re.search(r'(\d+)\s+maximum resident set size', timing)[1]) == attempt['peak_rss_bytes']
    assert int(re.search(r'(\d+)\s+swaps', timing)[1]) == attempt['swaps'] == 0
    lines = re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)", log)
    assert lines == attempt['axioms']
    if attempt['exit'] == 0:
        assert not attempt['errors']
        for line in lines:
            if 'depends on axioms:' in line:
                names = set(re.search(r'\[([^]]*)\]', line)[1].replace('\n', '').replace(' ', '').split(','))
                assert names <= allowed_axioms, line
    if attempt['final_current']:
        assert attempt['exit'] == 0
        source = PACKET / 'lean' / (attempt['module'] + '.lean')
        assert sha(source) == attempt['source_sha256']
        assert sha(attempt['argv'][7]) == attempt['object_sha256']
        final[attempt['module']] = attempt

freeze = json.loads((EVIDENCE / 'frozen-sources.json').read_text())
assert set(final) == {entry['module'] for entry in freeze['new_sources']}
theorem_count = 0
for entry in freeze['new_sources']:
    source = ROOT / entry['path']
    assert sha(source) == entry['sha256']
    code = re.sub(r'/\-[\s\S]*?\-/', '', source.read_text())
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|maxHeartbeats|maxRecDepth)\b', code)
    namespace = re.search(r'^namespace (\S+)', code, re.M)
    theorems = re.findall(r'^theorem (\w+)', code, re.M)
    for theorem in theorems:
        assert f'#print axioms {theorem}' in code
        full = namespace[1] + '.' + theorem
        assert any(line.startswith("'" + full + "'") for line in final[entry['module']]['axioms']), full
    theorem_count += len(theorems)

for entry in freeze['unchanged_sources']:
    assert sha(ROOT / entry['path']) == entry['sha256']
    base = subprocess.check_output(['git', 'show', freeze['base_revision'] + ':' + entry['path']], cwd=ROOT)
    assert hashlib.sha256(base).hexdigest() == entry['sha256']

before = signature('OraclePortHeadlineDVC7.lean')
after = signature('OraclePortShortCircuitHeadline.lean')
assert before == (EVIDENCE / 'headline-before.lean.txt').read_text()
assert after == (EVIDENCE / 'headline-after.lean.txt').read_text()
assert before.replace('(h_Rust_equals_dV : ExecutionJoin D rust)',
                      '(h_Rust_equals_dV : OuterExecutionJoin D rust)') == after
assert ''.join(difflib.unified_diff(before.splitlines(True), after.splitlines(True),
                                  fromfile='C7', tofile='outer-sc')) == (EVIDENCE / 'signature-retarget.diff').read_text()

changed = subprocess.check_output(['git', 'diff', '--name-only', freeze['base_revision']], cwd=ROOT, text=True).splitlines()
prefix = 'docs/research/100bit-spend-path-20261013/'
for path in changed:
    assert (path.startswith(prefix + 'lean/OraclePortShortCircuit') or
            path.startswith(prefix + 'evidence/shortcircuit-draft-20261021/') or
            path.startswith('tools/oracle-port-shortcircuit/') or
            path in {prefix + 'design/SHORTCIRCUIT-DRAFT-20261021.md',
                     prefix + 'design/JOIN-SPLIT-DRAFT-20261021.md'}), path
    if path.startswith(prefix + 'lean/'):
        existed = subprocess.run(['git', 'cat-file', '-e', freeze['base_revision'] + ':' + path],
                                 cwd=ROOT, stderr=subprocess.DEVNULL)
        assert existed.returncode != 0, 'Existing Lean module edited: ' + path

print(json.dumps({'attempts': len(manifest['attempts']), 'final_modules': len(final),
                  'new_theorems': theorem_count,
                  'accepted_axiom_reports': sum(len(a['axioms']) for a in manifest['attempts'] if a['exit'] == 0),
                  'failed_attempts': sum(a['exit'] != 0 for a in manifest['attempts']),
                  'peak_rss_bytes': max(a['peak_rss_bytes'] for a in manifest['attempts']),
                  'swaps': 0, 'status': 'focused packet verified; exact frozen-order port remains open'}, indent=2))
