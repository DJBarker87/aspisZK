#!/usr/bin/env python3
"""Read-only packet audit, plus deterministic signature artifacts."""
import difflib
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
PACKET = HERE.parent.parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest = json.loads((HERE / 'manifest.json').read_text())
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
modules = ['R9PoolCheckpointCodec', 'R9PoolSavedTenModel',
           'R9PoolConcreteExperiment', 'R9PoolRuntimeBinding', 'R9PoolP2Caller',
           'R1FinalSoundnessBinPerQueryR9Pool']
results = []
for module in modules:
    source = PACKET / 'lean' / (module + '.lean')
    candidates = [a for a in manifest['attempts'] if a['module'] == module and a['final_current']]
    assert len(candidates) == 1, (module, 'no unique accepted current attempt')
    rec = candidates[0]
    assert rec['exit'] == 0 and rec['swaps'] == 0
    assert rec['source_sha256'] == sha(source), module
    assert rec['peak_rss_bytes'] < 8 * 1024**3
    for imp in rec['direct_imports']:
        assert sha(imp['path']) == imp['sha256'], imp
    text = source.read_text()
    theorems = re.findall(r'^theorem\s+([^\s(]+)', text, re.M)
    assert len(rec['axioms']) == len(theorems), (module, len(theorems), rec['axioms'])
    for name in theorems:
        assert any(re.search(r"[.']" + re.escape(name) + "'", line) for line in rec['axioms']), name
    for line in rec['axioms']:
        bracket = re.search(r'\[([\s\S]*?)\]', line)
        if bracket:
            assert set(x.strip() for x in bracket[1].split(',')) <= allowed, line
        else:
            assert 'does not depend on any axioms' in line
    assert not re.search(r'\b(sorry|admit|native_decide)\b|set_option\s+(maxRecDepth|maxHeartbeats)', text)
    results.append({'module': module, 'attempt': rec['attempt'], 'axiom_audits': len(theorems),
                    'exit': 0, 'wall_seconds': rec['wall_seconds'],
                    'peak_rss_bytes': rec['peak_rss_bytes'], 'swaps': rec['swaps']})


def statement(path, name='final_soundness'):
    t = path.read_text()
    start = re.search(r'^theorem ' + name + r'\b', t, re.M).start()
    end = t.index(' := by', start)
    return t[start:end].replace('theorem ' + name, 'theorem final_soundness', 1) + '\n'

before = statement(PACKET / 'lean/R1FinalSoundnessBinPerQueryR9.lean')
after_path = PACKET / 'lean/R1FinalSoundnessBinPerQueryR9Pool.lean'
after = statement(after_path)
special = statement(after_path, 'final_soundness_with_transport')
line = next(line for line in special.splitlines(True) if '(h_R9_transport :' in line)
assert special.replace(line, '', 1) == after
assert 'h_R9_transport' not in after
# The compiled baseline must itself be just the original's model instance.
instantiated = before.replace('(Q : Nat) (tx1 : Tx1) (poolTx2 : PoolTx2)', '(Q : Nat) (tape : Tape) (policy : Policy)')
instantiated = instantiated.replace('deployedFailureModel tx1 poolTx2', 'deployedFailureModel (tx1 D P tape) (poolTx2 D d P policy)')
a = instantiated.index('    /- R9/R20:')
b = instantiated.index('    (h_R9_transport :', a)
instantiated = instantiated[:a] + instantiated[b:]
assert instantiated == special
for name, value in [('before-statement.lean.txt', before), ('specialized-before-statement.lean.txt', special),
                    ('after-statement.lean.txt', after), ('deleted-premise.lean.txt', line)]:
    (HERE / name).write_text(value)
for name, old, new in [('signature-full.diff', before, after), ('signature-deletion-only.diff', special, after)]:
    (HERE / name).write_text(''.join(difflib.unified_diff(old.splitlines(True), new.splitlines(True),
                                                     fromfile='before', tofile='after')))
source_map = json.loads((HERE / 'frozen-source-map.json').read_text())
for row in source_map['files']:
    assert row['equal_to_frozen'] and row['frozen_sha256'] == row['current_sha256']
    assert sha(row['path']) == row['current_sha256'], row['path']
changes = subprocess.check_output(['git', 'diff', '--name-status', '012f18382', '--',
    'docs/research/100bit-spend-path-20261013/lean'], text=True).splitlines()
assert len(changes) == len(modules), changes
assert all(line.startswith('A\t') and Path(line.split('\t')[1]).stem in modules for line in changes), changes
report = {'status': 'focused logical model packet; frozen Rust/ABI source join remains open',
          'schema': manifest['schema'], 'results': results,
          'total_axiom_audits': sum(r['axiom_audits'] for r in results),
          'additive_lean_sources_only': True, 'frozen_source_files_checked': len(source_map['files']),
          'signature': {'specialization_required': True, 'after_specialization_only_transport_deleted': True,
                        'arbitrary_source_premise_deletion_claimed': False}}
(HERE / 'audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
