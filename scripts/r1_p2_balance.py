#!/usr/bin/env python3
"""UNPROVED P2: select k from one completed k=0 diagnostic, no rerun."""
import json,sys
from pathlib import Path
p=Path(sys.argv[1])
a=json.loads((p/'measurements/transfer-diagnostic-k0-tx1-run1.json').read_text())
b=json.loads((p/'measurements/transfer-diagnostic-k0-tx2-run1.json').read_text())
assert a['verifier_completed'] and b['verifier_completed']
m=b['phase_markers']
start=next(x['remaining_cu'] for x in m if x['phase']=='checkpoint-read')
prefix=[0]+[start-x['remaining_cu'] for x in m if x['phase'].startswith('query:')]
assert len(prefix)==23
rows=[dict(k=k,tx1=a['verifier_cu']+x,tx2=b['verifier_cu']-x,peak=max(a['verifier_cu']+x,b['verifier_cu']-x)) for k,x in enumerate(prefix)]
best=min(rows,key=lambda r:r['peak'])
record=dict(label='UNPROVED COST PROBE; split prediction from the k=0 diagnostic',selected=best,candidates=rows,reason='The next diagnostic changes k; no unchanged measurement is repeated.')
assert not (p/'balance-selection.json').exists()
(p/'balance-selection.json').write_text(json.dumps(record,indent=2)+'\n')
print(best)
