#!/usr/bin/env python3
"""Read/hash only: exact emitted bytes, metadata-only adapter, and checked targets."""
from pathlib import Path
import argparse
import copy
import hashlib
import json
import re
import subprocess
import tarfile

ap = argparse.ArgumentParser(description=__doc__)
ap.add_argument('--git-source-check', action='store_true',
                help='also compare all466 recorded input hashes with pinned git blobs')
args = ap.parse_args()
base = Path(__file__).resolve().parent
repo = base.parents[4]
sha = lambda b: hashlib.sha256(b).hexdigest()
m = json.loads((base/'manifest.json').read_text())
archive = base/m['archive']
assert archive.stat().st_size == m['archive_bytes']
assert sha(archive.read_bytes()) == m['archive_sha256']
with tarfile.open(archive) as tf:
    members = tf.getmembers()
    assert all(x.isfile() or x.islnk() for x in members)
    assert len({x.name for x in members}) == len(members)
    f = {x.name: tf.extractfile(x).read() for x in members}
assert len(f) == m['archive_entries']
sums = dict((n,h) for h,n in
            (line.split('  ',1) for line in f['SHA256SUMS'].decode().splitlines()))
assert set(sums) == set(f)-{'SHA256SUMS'}
for n,h in sums.items():
    assert sha(f[n]) == h, n
raw_bytes = f['original/TerminalDecoder.llbc']
adapted_bytes = f['original/TerminalDecoder-renamed.llbc']
assert sha(raw_bytes) == m['raw_llbc_sha256']
assert sha(adapted_bytes) == m['renamed_llbc_sha256']
raw, adapted = json.loads(raw_bytes), json.loads(adapted_bytes)
assert not raw['has_errors'] and not adapted['has_errors']
report = json.loads(f['original/rename-report.json'])
assert report['input_sha256'] == sha(raw_bytes)
assert report['output_sha256'] == sha(adapted_bytes)
assert report['restored_complete_json_equals_input']
assert len(report['changes']) == 4
restored = copy.deepcopy(adapted)
for c in report['changes']:
    fn = restored['translated']['fun_decls'][c['function_index']]
    assert fn['def_id'] == c['def_id']
    assert fn['item_meta']['name'] == c['rust_name']
    assert fn['item_meta']['attr_info']['rename'] == c['new_rename']
    fn['item_meta']['attr_info']['rename'] = c['old_rename']
assert restored == raw
option = next(t for t in adapted['translated']['type_decls'] if t and t['def_id'] == 20)
assert [(v['name'],v['discriminant']) for v in option['kind']['Enum']] == [
    ('None',{'Scalar':{'Signed':['Isize','0']}}),
    ('Some',{'Scalar':{'Signed':['Isize','1']}})]
for name in ('Types','Funs'):
    original = f[f'original/{name}.lean']
    assert original == f[f'proofs/sources/AspisR1TerminalDecoder/{name}.lean']
    assert b'Slice.Insts.CoreCmpPartialEqArray.eq' not in original
    assert not re.search(rb'(?m)^\s*(axiom|opaque|sorry|admit)\b',original)
assert b'core.result.Result.unwrap' not in f['original/Funs.lean']
assert b'axiom Slice.Insts.CoreCmpPartialEqArray.eq' in f['original/FunsExternal_Template.lean']
compat = f['proofs/sources/AspisR1TerminalDecoder/FunsExternal.lean']
assert not re.search(rb'(?m)^\s*(axiom|opaque|sorry|admit)\b',compat)
standard = {'propext','Classical.choice','Quot.sound'}
count = 0
for name, record in m['modules'].items():
    relative = name.replace('.','/')
    src = f[f'proofs/sources/{relative}.lean']
    assert sha(src) == record['source_sha256']
    assert (repo/record['source']).read_bytes() == src
    r = json.loads(f[record['receipt']])
    assert r['exit_status'] == 0 and r['axioms']['passed']
    assert r['source_revision'] == m['rust_source_revision']
    assert r['key']['source_sha256'] == sha(src)
    assert r['process_swaps'] == 0 and r['cgroup_swap_current'] == '0'
    assert r['limits'] == {'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
    for key in ('exit_status','wall_seconds','peak_process_rss_kib',
                'sampled_cgroup_peak_bytes','cgroup_memory_peak_cumulative',
                'process_swaps','axioms','objects'):
        assert r[key] == record[key]
    for suffix,obj in r['objects'].items():
        assert sha(f[f'proofs/objects/{relative}{suffix}']) == obj['sha256']
    for a in r['axioms']['reports']:
        assert set(a['axioms']) <= standard
        count += 1
assert count == m['standard_only_reports'] == 18
actual = m['modules']['TerminalDecoderGeneratedAudit']['axioms']
assert len(actual['reports']) == actual['requested_count'] == 16
helper = [r for r in actual['reports'] if r['declaration'].endswith('.unwrap_fixed_slice')]
assert helper == [m['helper_report']] and helper[0]['axioms'] == []
assert all(set(r['axioms']) == standard for r in actual['reports'] if r not in helper)
pins = json.loads(f['original/repository-source-pins.json'])
check = json.loads(f['original/repository-source-check.json'])
assert pins['revision'] == check['revision'] == m['rust_source_revision']
assert len(pins['files']) == check['count'] == 466 and check['mismatches'] == []
snapshots = {n:v for n,v in f.items() if n.startswith('original/source/')}
assert len(snapshots) == 6
for n,data in snapshots.items():
    assert sha(data) == pins['files'][n.removeprefix('original/source/')]
if args.git_source_check:
    for path,h in pins['files'].items():
        blob = subprocess.check_output(['git','show',pins['revision']+':'+path],cwd=repo)
        assert sha(blob) == h, path
for label in ('charon-a','aeneas-a'):
    r = json.loads(f[f'original/{label}/receipt.json'])
    assert r == m['extraction'][label]
    assert r['exit_status'] == 0 and r['swaps'] == 0
    assert r['source_revision'] == m['rust_source_revision']
print(f'PASS: {len(f)} logical members; unchanged emitted sources; four-name inverse; four checked targets; helper[] plus15standard reports and2Option tags. Decoder correctness remains OPEN.')
