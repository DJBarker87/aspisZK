#!/usr/bin/env python3
"""Validate the source-only tx2_common full-body proof packet."""
import hashlib, json
from pathlib import Path
ROOT = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((ROOT / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
assert manifest['packet'] == ROOT.name
for module in manifest['modules']:
    assert sha(ROOT / module['source']) == module['source_sha256']
    receipt = json.loads((ROOT / module['producer_receipt']).read_text())
    assert receipt['source_sha256'] == module['source_sha256']
    assert receipt['exit_status'] == 0
    assert module['swap_bytes'] == 0
    assert module['axioms'] == ['propext', 'Classical.choice', 'Quot.sound']
for name, pin in manifest['direct_import_source_map'].items():
    assert sha((ROOT / pin['source_path']).resolve()) == pin['source_sha256'], name + ' source'
    assert sha((ROOT / pin['selected_object_path']).resolve()) == pin['object_sha256'], name + ' object'
for name, pin in manifest['source_bindings'].items():
    assert sha(ROOT / pin['path']) == pin['sha256'], name
for entry in manifest.get('files', []):
    assert sha(ROOT / entry['path']) == entry['sha256'], entry['path']
assert not list(ROOT.rglob('*.olean')), 'packet must remain source-only'
assert not list(ROOT.rglob('*.ilean')), 'packet must remain source-only'
assert 'tx2CommonFullSourceCut_success_reaches_query_loop' in (ROOT/'sources/S4Tx2FullSourceOwnedCutV1.lean').read_text()
print('PASS: source-only full-body packet, imported owner pins, producer receipt, axioms, no compiled objects')
