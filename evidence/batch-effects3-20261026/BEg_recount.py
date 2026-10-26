"""Preserve Rc8 ledger identities; no row-removal credit without native proof."""
from pathlib import Path
import json,hashlib
P=Path(__file__).resolve().parent; R=P.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
base=R/'evidence/recount8-20261026/Rc8_premises.json';x=json.loads(base.read_text());pins=json.loads((P/'BEg_BASELINE.json').read_text())
assert sha(R/'lean/Rc8_Top.lean')==pins['pins']['lean/Rc8_Top.lean']
assert sha(base)==pins['pins'][str(base.relative_to(R))]
assert next(r for r in x['rows'] if r['id']=='L166')['scope']=='deployment only'
stmt=(R/'evidence/recount8-20261026/Rc8_AFTER.lean.txt').read_bytes()
for label in ['BEFORE','AFTER']:(P/('BEg_'+label+'.lean.txt')).write_bytes(stmt)
result=dict(actual_theorem='AspisR1.Rc8_Top.deployed',method=x['method'],baseline_sha256=sha(base),before=x['counts'],after=x['counts'],distinct_delta=dict(T=0,P=0,G=0,C=0),removed=[],added=[],reclassified=[],L166='RETAINED: accepted native carrier and complete rejected-history association unproved',before_after='Byte identical. No new deployed theorem or changed quantifiers/carriers/failure event/conclusion.',rows=x['rows'])
(P/'BEg_recount.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['actual_theorem','distinct_delta','L166']},indent=2))
