#!/usr/bin/env python3
"""Read/hash the focused proof receipt and its exact retained import closure."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

base = Path(__file__).resolve().parent
repo = base.parents[4]
sha = lambda b: hashlib.sha256(b).hexdigest()
digest = lambda j: sha(json.dumps(j, sort_keys=True).encode())
m = json.loads((base / 'manifest.json').read_text())
p = base / m['archive']
assert p.stat().st_size == m['archive_bytes']
assert sha(p.read_bytes()) == m['archive_sha256']
with tarfile.open(p) as tf:
    members = tf.getmembers()
    assert all(x.isfile() or x.islnk() for x in members)
    assert len({x.name for x in members}) == len(members)
    files = {x.name: tf.extractfile(x).read() for x in members}
assert len(files) == m['archive_entries']
sums = dict((n, h) for h, n in
            (line.split('  ', 1) for line in files['SHA256SUMS'].decode().splitlines()))
assert set(sums) == set(files) - {'SHA256SUMS'}
for n, h in sums.items():
    assert sha(files[n]) == h, n
assert sha(files['proofs/runner.py']) == m['runner_sha256']
snapshot_bytes = files['proofs/runs/success-d/external-inputs.json']
assert sha(snapshot_bytes) == m['external_snapshot_sha256']
snapshot = json.loads(snapshot_bytes)
assert snapshot['lean_version'] == '4.32.0'
keys = {}
def external_key(name):
    if name not in keys:
        x = snapshot['modules'][name]
        keys[name] = digest({'source': x['source_sha256'],
                            'objects': {s: o['sha256'] for s, o in x['objects'].items()},
                            'imports': {d: external_key(d) for d in x['imports']},
                            'runtime': snapshot['runtime_files']})
    return keys[name]

standard = {'propext', 'Classical.choice', 'Quot.sound'}
for name, r in m['modules'].items():
    assert json.loads(files[f'proofs/successful-targets/{name}.json']) == r
    rel = name.replace('.', '/')
    src = files[f'proofs/sources/{rel}.lean']
    assert sha(src) == r['key']['source_sha256']
    assert (repo / r['source_manifest_entry']['source']).read_bytes() == src
    assert r['exit_status'] == 0 and r['axioms']['passed']
    assert r['key']['runtime'] == snapshot['runtime_files']
    assert r['process_swaps'] == 0 and r['cgroup_swap_current'] == '0'
    assert r['limits'] == {'memory.high': '6442450944',
                           'memory.max': '8589934592', 'memory.swap.max': '0'}
    for suffix, obj in r['objects'].items():
        assert sha(files[f'proofs/objects/{rel}{suffix}']) == obj['sha256']
    for dep, item in r['key']['imports'].items():
        if dep in m['modules']:
            predecessor = m['modules'][dep]
            assert item == {'receipt_key': digest(predecessor['key']),
                            'objects': predecessor['objects']}
        else:
            assert item == {'closure_key': external_key(dep),
                            'objects': snapshot['modules'][dep]['objects']}
    assert all(set(a['axioms']) <= standard for a in r['axioms']['reports'])

target = m['modules'][m['target']]
assert target['source_revision'] == m['proof_base_revision']
assert target['axioms']['requested_count'] == 3
assert len(target['axioms']['reports']) == 3
assert all(set(a['axioms']) == standard for a in target['axioms']['reports'])
src = files['proofs/sources/ExtractedTerminalDecoderSuccess.lean']
assert not re.search(rb'\b(sorry|admit|axiom|opaque)\b', src)
for label, r in m['attempts'].items():
    prefix = f'proofs/runs/{label}/ExtractedTerminalDecoderSuccess/'
    assert json.loads(files[prefix + 'receipt.json']) == r
    assert sha(files[prefix + 'source.lean']) == r['key']['source_sha256']
    if label == 'success-d':
        assert r == target
        log = files[prefix + 'lean.log'].decode()
        reports = [{'declaration': n, 'axioms': [a.strip() for a in v.split(',') if a.strip()]}
                   for n, v in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]", log, re.S)]
        assert reports == target['axioms']['reports']
    else:
        assert r['exit_status'] == 1 and not r['axioms']['passed']

old = json.loads((base / m['generated_cone_evidence']).read_text())
assert old['rust_source_revision'] == m['rust_source_revision']
for name in ('AspisR1TerminalDecoder.Types', 'AspisR1TerminalDecoder.FunsExternal',
             'AspisR1TerminalDecoder.Funs'):
    r = m['modules'][name]
    assert r['source_revision'] == m['rust_source_revision']
    assert r['key']['source_sha256'] == old['modules'][name]['source_sha256']
    assert r['objects'] == old['modules'][name]['objects']
print(f"PASS: {len(files)} members; three retained failures; exact generated import receipts; "
      "actual decoder-success proof and three standard-only reports. Runtime preservation remains OPEN.")
