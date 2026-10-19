#!/usr/bin/env python3
import hashlib, json
from pathlib import Path
E=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for line in (E/'SHA256SUMS').read_text().splitlines():
    expected,rel=line.split('  ',1)
    path=E/rel
    assert path.is_file(),rel
    assert sha(path)==expected,rel
r=json.loads((E/'attempts/b/receipt.json').read_text())
p=json.loads((E/'attempts/b/preflight.json').read_text())
s=json.loads((E/'summary.json').read_text())
assert r['all_passed'] is True and len(r['results'])==2
assert [x['exit'] for x in r['results']]==[0,0]
assert '10 passed; 0 failed' in (E/'attempts/b/test-1.log').read_text()
assert '6 passed; 0 failed' in (E/'attempts/b/test-2.log').read_text()
assert all(x['swap_current_bytes']==0 for x in r['results'])
assert p['source_revision']==s['source_revision']
assert p['source_file_pins']==s['candidate_sources']
assert p['limits']=={'memory.high':'8589934592','memory.max':'10737418240','memory.swap.max':'0','pids.max':'128'}
assert not s['settlement_exercised']
print('candidate module test evidence checks passed')
