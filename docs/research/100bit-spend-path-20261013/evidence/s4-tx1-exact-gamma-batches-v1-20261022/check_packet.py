#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).parent
sha=lambda f:hashlib.sha256(Path(f).read_bytes()).hexdigest()
for rel in ['prep-bridge','full-consumer']:
 r=json.loads((p/'receipt'/rel/'receipt.json').read_text())
 assert r['exit_status']==0 and r['watchdog_abort'] is None and r['process_swaps']==0
 assert r['source_sha256']==sha(p/('sources/S4Tx1ExactGammaBatchesRootV1.lean' if rel=='prep-bridge' else 'sources/S4Tx1WholeExactBatchesRootV1.lean'))
 assert r['object_sha256'] and r['peak_aggregate_rss_bytes']>0 and r['wall_seconds']>0
 ax=(p/'receipt'/rel/'axioms.txt').read_text()
 assert 'sorryAx' not in ax and all(x in ax for x in ['propext','Classical.choice','Quot.sound'])
 cmd=json.loads((p/'receipt'/rel/'command.json').read_text())
 assert '-j1' in cmd['argv'] and '4400' in cmd['argv']
 assert not list((p/'receipt'/rel).rglob('*.olean'))
pins=json.loads((p/'receipt/direct-import-pins.json').read_text())
for name,v in pins.items():
 assert sha(v['source'])==v['source_sha256'],name+' source changed'
 assert sha(v['object'])==v['object_sha256'],name+' object changed'
assert not list(p.rglob('*.olean'))
for line in (p/'SHA256SUMS').read_text().splitlines():
 expected,rel=line.split('  ',1); assert sha(p/rel)==expected,rel
print('PASS')
