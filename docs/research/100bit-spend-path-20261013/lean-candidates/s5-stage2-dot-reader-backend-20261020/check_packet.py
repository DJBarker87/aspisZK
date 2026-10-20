#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (D/'SHA256SUMS').read_text().splitlines():
 h,f=line.split('  ',1); assert sha(D/f)==h,f
pins=json.loads((D/'naming-adapter.json').read_text());original=(D/'sources/Stage2ContinuationTypes.original.lean').read_text();adapted=(D/'sources/Stage2ContinuationTypes.lean').read_text()
assert hashlib.sha256(original.encode()).hexdigest()==pins['original_sha256']
assert hashlib.sha256(adapted.encode()).hexdigest()==pins['adapter_sha256']
for c in reversed(pins['changes']):
 assert adapted.count(c['replacement'])==1;adapted=adapted.replace(c['replacement'],c['original'])
assert adapted==original
for m in json.loads((D/'manifest.json').read_text())['modules']:
 assert sha(D/m['source'])==m['source_sha256']; r=json.loads((D/m['receipt']).read_text());assert r['exit_status']==0 and r['scope_swap_peak_bytes']==0
r=json.loads((D/'evidence/original-discriminant-audit/receipt.json').read_text());assert r['exit_status']==0 and r['scope_swap_peak_bytes']==0
assert (D/'evidence/original-discriminant-audit/preflight.json').is_file()
print('PASS: pinned sources, inverse naming adapter, focused receipts, no-binary publication')
