#!/usr/bin/env python3
"""Audit the public R122 receipt and theorem boundary."""
import hashlib, json
from pathlib import Path
root=Path(__file__).parents[1]
evidence=root/'evidence/r122-adaptive-first-read'
manifest=json.loads((Path(__file__).with_name('r122-release-manifest.json')).read_text())
receipt=json.loads((evidence/'receipt.json').read_text())
assert receipt['base_revision']==manifest['base_revision']
assert receipt['status']=='PASS' and receipt['compiled']==2
assert receipt['memory_swap_max']==0
assert [x['target'] for x in receipt['targets']]==[x['target'] for x in manifest['targets']]
for item in manifest['targets']:
    path=root/'lean'/(item['target']+'.lean')
    assert hashlib.sha256(path.read_bytes()).hexdigest()==item['sha256']
for target in receipt['targets']:
    assert target['exit']==0 and target['swap']==0 and target['peak_rss_kib']<7*1024*1024
    assert 'sorryAx' not in target['axioms']
    assert 'propext, Classical.choice and Quot.sound' in target['axioms']
assert receipt['claims']['fixed_root_bound']=='819 / (2147483647^4)'
assert receipt['claims']['actual_source_freshness']=='OPEN'
assert receipt['claims']['full_privacy'] is False
assert receipt['claims']['full_soundness'] is False
print(json.dumps({'status':'PASS','compiled':2,'axiom_audits':receipt['axiom_audits'],
    'first_remaining':receipt['first_remaining']}))
