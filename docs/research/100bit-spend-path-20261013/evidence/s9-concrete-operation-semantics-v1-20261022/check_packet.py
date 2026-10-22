#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent
m = json.loads((root / 'manifest.json').read_text())
assert m['schema'] == 'focused-extractor-proof-packet-v1'
assert m['status'].startswith('source-only')
assert len(m['proofs']) == 2
for proof in m['proofs']:
    src = root / proof['source']
    assert hashlib.sha256(src.read_bytes()).hexdigest() == proof['source_sha256']
    assert proof['exit_code'] == 0 and proof['swap_bytes'] == 0
    assert proof['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
    assert pathlib.Path(proof['object_external_path']).is_file()
    assert hashlib.sha256(pathlib.Path(proof['object_external_path']).read_bytes()).hexdigest() == proof['object_sha256']
for src in m['selected_external_sources'].values():
    p = pathlib.Path('/Users/dominic/ZK') / src['path']
    assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest() == src['sha256']
for owner in m['selected_external_owners'].values():
    p = pathlib.Path(owner['path'])
    assert p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest() == owner['sha256']
closure = json.loads((root / m['import_closure']['path']).read_text())
assert closure['modules'] == m['import_closure']['modules'] and not closure['missing']
assert not list(root.rglob('*.olean'))
expected = sorted(str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name != 'SHA256SUMS')
lines = (root / 'SHA256SUMS').read_text().splitlines()
assert sorted(line.split('  ',1)[1] for line in lines) == expected
for line in lines:
    digest, rel = line.split('  ',1)
    assert hashlib.sha256((root/rel).read_bytes()).hexdigest() == digest
print('PASS')
