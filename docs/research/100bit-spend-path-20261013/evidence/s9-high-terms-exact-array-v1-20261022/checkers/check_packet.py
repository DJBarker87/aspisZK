#!/usr/bin/env python3
import hashlib, json, pathlib, sys
root = pathlib.Path(__file__).resolve().parents[1]
manifest = json.loads((root / 'manifest.json').read_text())
assert manifest['schema'] == 'focused-extractor-proof-packet-v1'
expected_axioms = '[propext, Classical.choice, Quot.sound]'
for item, receipt_name, log_name in [
    (manifest['theorems'][0], 'onecall-receipt.json', 'onecall-lean.log'),
    (manifest['theorems'][1], 'step-receipt.json', 'step-lean.log'),
    (manifest['theorems'][2], 'trace-receipt.json', 'trace-lean.log'),
]:
    source = root / item['source']
    assert hashlib.sha256(source.read_bytes()).hexdigest() == item['source_sha256'], item['module']
    obj = pathlib.Path(item['compiled_object_external_path'])
    assert obj.is_file(), str(obj)
    assert hashlib.sha256(obj.read_bytes()).hexdigest() == item['object_sha256'], item['module']
    receipt = json.loads((root / 'receipts' / receipt_name).read_text())
    assert receipt['exit_status'] == 0, item['module']
    assert receipt['source_sha256'] == item['source_sha256'], item['module']
    assert receipt['object_sha256'] == item['object_sha256'], item['module']
    assert receipt['process_swaps'] == 0, item['module']
    log = (root / 'receipts' / log_name).read_text()
    assert expected_axioms in log, (item['module'], log)
    assert 'sorryAx' not in log and 'admitAx' not in log, item['module']
    assert (root / 'profiles' / (receipt_name.removesuffix('-receipt.json') + '-LEAN_PATH.txt')).is_file()
print('PASS: packet schema, source/object pins, successful zero-swap receipts, selected profiles, and standard axiom reports verified')
