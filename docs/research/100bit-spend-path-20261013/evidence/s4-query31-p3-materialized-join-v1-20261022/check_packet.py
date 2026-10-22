#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, sys
ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((ROOT / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert manifest['result'] == 'green'
for item in manifest['files']:
    path = ROOT / item['path']
    assert path.is_file(), item['path']
    assert path.stat().st_size == item['size'], item['path']
    assert sha(path) == item['sha256'], item['path']
receipt = json.loads((ROOT / 'attempt/receipt.json').read_text())
assert receipt['exit_status'] == 0
assert receipt['source_sha256'] == sha(ROOT / 'sources/S4Query31P3MaterializedJoinV1.lean')
assert receipt['object_sha256'] == manifest['compiled_object_sha256']
log = (ROOT / 'attempt/lean.log').read_text()
assert "actual_query_row31_solana_p3_materialized_join' depends on axioms: [propext," in log
assert 'Classical.choice' in log and 'Quot.sound' in log and 'sorryAx' not in log
pins = json.loads((ROOT / 'attempt/direct-import-pins.json').read_text())
for name, pin in pins.items():
    src = Path('/Users/dominic/ZK') / pin['source']
    obj = Path(pin['object'])
    assert src.is_file() and sha(src) == pin['source_sha256'], name + ' source'
    assert obj.is_file() and sha(obj) == pin['object_sha256'], name + ' object'
for p in ROOT.rglob('*'):
    if p.is_file():
        assert p.suffix not in {'.olean', '.ilean', '.c', '.o'}, f'unexpected compiled artifact: {p}'
print('PASS: source-only row31 P3 specialization packet and named standard axioms')
