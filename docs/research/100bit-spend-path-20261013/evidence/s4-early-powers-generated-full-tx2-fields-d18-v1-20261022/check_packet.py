#!/usr/bin/env python3
from pathlib import Path
import hashlib, json, re
ROOT=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()

# Exact changed sources and frozen producer receipt binding.
for src,receipt in [
    ('sources/S4EarlyPowersSourceBindingV1.lean','producer/early-binding/receipt.json'),
    ('sources/S4Tx2EarlyPowersCandidateFieldsD18V1.lean','producer/full-tx2-consumer/receipt.json'),
    ('sources/S4Tx2EarlyPowersReturnedLocalBatchesV1.lean','producer/returned-local-batches/receipt.json'),
]:
    r=json.loads((ROOT/receipt).read_text())
    assert sha(ROOT/src)==r['source_sha256'], (src,sha(ROOT/src),r['source_sha256'])
    assert r['exit_status']==0 and r['object_sha256']
    assert r['swaps'] is None
    log=(ROOT/receipt).with_name('lean.log').read_text()
    assert 'sorryAx' not in log
    for ax in ('propext','Classical.choice','Quot.sound'):
        assert ax in log

# The local repaired CurrentClaim owner is byte-identical to the pinned S1 owner.
r=json.loads((ROOT/'producer/early-owner-rebuild/receipt.json').read_text())
assert r['exit_status']==0
assert r['source_sha256']=='083f42ed38f40a6f04ed2590124beaea1cca306f369046667ba87c645d2a0ae1'
assert r['object_sha256']=='6b07dbe21413b16be7305b7e835b6a6cead7c86368863dcb22729504a82f048f'

pins=json.loads((ROOT/'producer/import-pins.json').read_text())
for name,item in pins.items():
    assert sha(ROOT/'source-pins'/('s1/'+name+'.lean'))==item['source_sha256']
    assert item['selected_object_sha256']

closure=json.loads((ROOT/'producer/import-closure/closure.json').read_text())
assert closure['modules']==7498 and closure['missing']==[]
assert sha(ROOT/'producer/import-closure/closure.json')==hashlib.sha256((ROOT/'producer/import-closure/closure.json').read_bytes()).hexdigest()

assert not list(ROOT.rglob('*.olean')), 'compiled objects are excluded from source-only evidence'
print('PASS: source/object receipts, standard-only axiom logs, candidate pins, and zero-missing import closure')
