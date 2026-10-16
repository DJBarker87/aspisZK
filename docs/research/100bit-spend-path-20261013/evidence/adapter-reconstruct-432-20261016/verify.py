#!/usr/bin/env python3
"""Read/hash only: verify pinned cut, original emission, and actual checked receipts."""
from pathlib import Path
import hashlib, json, re, tarfile, tomllib
base = Path(__file__).resolve().parent
repo = base.parents[4]
sha = lambda b: hashlib.sha256(b).hexdigest()
m = json.loads((base/'manifest.json').read_text())
archive = base/m['archive']
assert sha(archive.read_bytes()) == m['archive_sha256']
with tarfile.open(archive) as tf:
    members = tf.getmembers()
    assert all(x.isfile() or x.islnk() for x in members)
    assert len({x.name for x in members}) == len(members)
    f = {x.name: tf.extractfile(x).read() for x in members}
assert len(f) == m['archive_entries']
sums = dict((n,h) for h,n in (line.split('  ',1) for line in f['SHA256SUMS'].decode().splitlines()))
assert set(sums) == set(f)-{'SHA256SUMS'}
for n,h in sums.items(): assert sha(f[n]) == h, n
pins = json.loads(f['input/source-pins.json'])
for n,h in pins['kit_files'].items(): assert sha(f['input/'+n]) == h, n
original = json.loads(f['repository-source-pins.json'])
for n,h in original['files'].items():
    if n not in ('Cargo.toml','Cargo.lock'): assert sha(f['input/'+n]) == h, n
assert sha(f['input/Cargo.lock.original']) == original['files']['Cargo.lock']
old = tomllib.loads(f['input/Cargo.lock.original'].decode())['package']
new = tomllib.loads(f['input/Cargo.lock'].decode())['package']
assert all(p in new for p in old)
assert [p['name'] for p in new if p not in old] == ['aspis-r1-adapter-reconstruct']
kit = repo/'docs/research/100bit-spend-path-20261013/tools/adapter-reconstruct-extraction-kit'
cutpins = json.loads((kit/'source-pins.json').read_text())
source = f['input/'+cutpins['source_path']]
assert sha(source) == cutpins['source_sha256']
for c in cutpins['cuts']:
    chunk = b''.join(source.splitlines(keepends=True)[c['start_line']-1:c['end_line']])
    assert sha(chunk) == c['sha256'], c['name']
for n in ('lib.rs','Cargo.toml','source-pins.json','extract.py'):
    assert (kit/n).read_bytes() == f['input/programs/adapter-reconstruct/'+n], n
raw_llbc = json.loads(f['extraction-a/AdapterReconstruct.llbc'])
assert not raw_llbc['has_errors']
llbc = raw_llbc['translated']
t = next(t for t in llbc['type_decls'] if t and t['def_id']==7)
assert [(v['name'],v['discriminant']) for v in t['kind']['Enum']] == [
    ('None',{'Scalar':{'Signed':['Isize','0']}}),('Some',{'Scalar':{'Signed':['Isize','1']}})]
for kind in ('type_decls','fun_decls'):
    assert not any(re.search(r'QM31|CM31', json.dumps(x['item_meta']['name'])) for x in llbc[kind] if x)
for n in ('Types','Funs'):
    generated = f['extraction-a/generated/AspisR1AdapterReconstruct/'+n+'.lean']
    assert generated == f['proofs/sources/AspisR1AdapterReconstruct/'+n+'.lean']
    assert b'Slice.Insts.CoreCmpPartialEqArray.eq' not in generated
    assert not re.search(rb'(?m)^\s*(axiom|opaque|sorry|admit)\b',generated)
allowed = {'propext','Classical.choice','Quot.sound'}
for name, record in m['modules'].items():
    src = f['proofs/sources/'+name.replace('.','/')+'.lean']
    assert sha(src)==record['source_sha256']
    assert (repo/record['source']).read_bytes()==src
    r = json.loads(f[record['receipt']])
    assert r['exit_status']==0 and r['axioms']['passed']
    assert r['key']['source_sha256']==record['source_sha256']
    assert r['process_swaps']==0 and r['cgroup_swap_current']=='0'
    for report in r['axioms']['reports']: assert set(report['axioms']) <= allowed
    for suffix,obj in r['objects'].items():
        assert sha(f['proofs/objects/'+name.replace('.','/')+suffix])==obj['sha256']
for attempt in m['retained_failed_proof_attempts']:
    r=json.loads(f['proofs/runs/'+attempt+'/ExtractedAdapterReconstructSuccess/receipt.json'])
    assert r['exit_status'] != 0 and not r['axioms']['passed']
for n in ('charon-a','aeneas-a'):
    r=json.loads(f['runs/'+n+'/receipt.json'])
    assert r['exit_status']==0 and r['swaps']==0
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0'}
assert m['standard_only_report_count']==10
print(f"PASS: {len(f)} logical archive members; exact cut/emission; five checked modules, ten standard-only reports; three failed attempts retained")
