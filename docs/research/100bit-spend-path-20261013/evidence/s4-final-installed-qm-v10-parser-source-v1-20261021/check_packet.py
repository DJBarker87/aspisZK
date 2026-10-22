#!/usr/bin/env python3
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
REPO=ROOT.parents[4]
m=json.loads((ROOT/'manifest.json').read_text())
r=json.loads((ROOT/'evidence/receipt.json').read_text())
def sha(p):
 p=Path(p)
 if not p.is_absolute(): p=REPO/p
 return hashlib.sha256(p.read_bytes()).hexdigest()
assert r['exit_status']==0 and r['watchdog_abort'] is None
assert r['process_swaps']==0
assert sha(ROOT/m['source'])==m['source_sha256']==r['source_sha256']
assert sha(m['object_path'])==m['object_sha256']==r['object_sha256']
assert sha(m['compiler']['path'])==m['compiler']['sha256']
for _,v in m['direct_imports'].items():
 assert sha(v['source'])==v['source_sha256']
 assert sha(v['object_path'])==v['object_sha256']
assert sha(m['transitive_carrier_owner']['source'])==m['transitive_carrier_owner']['source_sha256']
assert sha(m['transitive_carrier_owner']['object_path'])==m['transitive_carrier_owner']['object_sha256']
log=(ROOT/'evidence/lean.log').read_text()
for t in m['theorems']:
 assert t in log
 assert 'sorryAx' not in log
for attempt in ('attempt-v1','attempt-v2'):
 d=ROOT/'evidence/diagnostics'/attempt
 assert (d/'lean.log').exists() and (d/'rejected-source.lean').exists()
print('PASS: final installed QM parser bridge pins, measured receipt, standard axioms and rejected diagnostics verified')
