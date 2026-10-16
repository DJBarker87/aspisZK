#!/usr/bin/env python3
"""Read/hash only; preserve the two failed gates without promoting either."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import tarfile

base = Path(__file__).resolve().parent
sha = lambda b: hashlib.sha256(b).hexdigest()
m = json.loads((base / 'manifest.json').read_text())
archive = base / m['archive']
assert archive.stat().st_size == m['archive_bytes']
assert sha(archive.read_bytes()) == m['archive_sha256']
with tarfile.open(archive) as tf:
    members = tf.getmembers()
    assert all(x.isfile() or x.islnk() for x in members)
    assert len({x.name for x in members}) == len(members)
    f = {x.name: tf.extractfile(x).read() for x in members}
assert len(f) == m['archive_entries']
sums = dict((n, h) for h, n in
            (line.split('  ', 1) for line in f['SHA256SUMS'].decode().splitlines()))
assert set(sums) == set(f) - {'SHA256SUMS'}
for n, h in sums.items():
    assert sha(f[n]) == h, n

standard = {'propext', 'Classical.choice', 'Quot.sound'}
for label, record in m['attempts'].items():
    r = json.loads(f[record['receipt']])
    for k in ('target', 'exit_status', 'source_revision', 'wall_seconds',
              'peak_process_rss_kib', 'sampled_cgroup_peak_bytes',
              'process_swaps', 'limits', 'axioms'):
        assert r[k] == record[k], (label, k)
    variant = label.split('/')[0]
    relative = r['target'].replace('.', '/')
    src = f[f'{variant}/proofs/sources/{relative}.lean']
    assert sha(src) == r['key']['source_sha256'] == record['source_sha256']
    assert r['process_swaps'] == 0 and r['cgroup_swap_current'] == '0'
    assert r['limits'] == {'memory.high': '6442450944',
                           'memory.max': '8589934592', 'memory.swap.max': '0'}
    promoted = f'{variant}/proofs/successful-targets/{r["target"]}.json'
    failed = label in ('layout80/funs-a', 'geometry1024/audit-a')
    assert (promoted not in f) == failed
    if not failed:
        assert r['exit_status'] == 0 and r['axioms']['passed']
        assert f[promoted] == f[record['receipt']]
        for report in r['axioms']['reports']:
            assert set(report['axioms']) <= standard
        for suffix, obj in r['objects'].items():
            assert sha(f[f'{variant}/proofs/objects/{relative}{suffix}']) == obj['sha256']
old = m['attempts']['layout80/funs-a']
assert old['exit_status'] == 1 and old['axioms']['requested_count'] == 0
oldlog = f['layout80/proofs/runs/funs-a/AspisR1TerminalDecoder.Funs/lean.log']
assert b'3241' in oldlog and b'5286' in oldlog
audit = m['attempts']['geometry1024/audit-a']
assert audit['exit_status'] == 0 and not audit['axioms']['passed']
reports = audit['axioms']['reports']
assert len(reports) == audit['axioms']['requested_count'] == 15
assert reports[0]['declaration'].endswith('.M31.from_le_bytes')
assert set(reports[0]['axioms']) <= standard
assert all(set(r['axioms']) == standard | {'Aeneas.Std.core.fmt.Formatter'}
           for r in reports[1:])

pins = json.loads(f['layout80/diagnosis/source-pins.json'])
for n, h in pins['files'].items():
    assert sha(f['layout80/diagnosis/' + n]) == h
llbc_bytes = f['layout80/original/TerminalDecoder-renamed.llbc']
assert sha(llbc_bytes) == m['original_llbc_sha256']
llbc = json.loads(llbc_bytes)
assert not llbc['has_errors']
option = next(t for t in llbc['translated']['type_decls'] if t and t['def_id'] == 20)
assert [(v['name'], v['discriminant']) for v in option['kind']['Enum']] == [
    ('None', {'Scalar': {'Signed': ['Isize', '0']}}),
    ('Some', {'Scalar': {'Signed': ['Isize', '1']}})]
tool = base.parents[1] / 'tools/j1a-compare-lean-layout.py'
assert tool.read_bytes() == f['layout80/diagnosis/compare-lean-layout.py']
spec = importlib.util.spec_from_file_location('layout_compare', tool)
comparator = importlib.util.module_from_spec(spec)
spec.loader.exec_module(comparator)
for n, count in (('Types', 1458), ('Funs', 17672)):
    original = f[f'layout80/original/{n}.lean']
    assert original == f[f'layout80/proofs/sources/AspisR1TerminalDecoder/{n}.lean']
    candidate = f[f'geometry1024/proofs/sources/AspisR1TerminalDecoder/{n}.lean']
    left, right = comparator.tokens(original.decode()), comparator.tokens(candidate.decode())
    assert left == right and len(left) == count
    assert b'Slice.Insts.CoreCmpPartialEqArray.eq' not in original + candidate
    assert not re.search(rb'(?m)^\s*(axiom|opaque|sorry|admit)\b', original + candidate)
    recorded = json.loads(f[f'layout80/diagnosis/{n.lower()}-token-comparison.json'])
    assert recorded['original_sha256'] == sha(original)
    assert recorded['candidate_sha256'] == sha(candidate)
    assert recorded['token_sequences_equal']
tests = [
    ('def f := 1', 'def  f\n := 1', True),
    ('"a b"', '"ab"', False), ('/- a b -/', '/- ab -/', False),
    ('A.b', 'A . b', False), ('«a b»', '«ab»', False),
    ('/- a /- b -/ c -/', '/- a /- b -/ d -/', False),
    ('12', '1 2', False), (':=', ': =', False),
]
for a, b, expected in tests:
    assert (comparator.tokens(a) == comparator.tokens(b)) == expected
for bad in ('def f := $a', '"unterminated', '/- unterminated', '«unterminated'):
    try:
        comparator.tokens(bad)
    except ValueError:
        pass
    else:
        raise AssertionError(bad)
assert len(json.loads(f['layout80/diagnosis/lexical-comparator-tests.json'])['checks']) == 12
print(f'PASS diagnostic integrity: {len(f)} members; original layout failure; geometry compile then 14/15 Formatter audit rejection; 12 lexer checks. No decoder closure claimed.')
