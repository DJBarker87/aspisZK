"""Focused controls for the added complete Result/state/effects requirement."""
from pathlib import Path
import json,copy
import NEV_composition as m
E=Path(__file__).resolve().parent
c,p,prepare,validate=m.context();base=m.obj(E.parent/'native-ledger3-20261029/NDT_LEDGER.json');edges=prepare(base);results=[]
for label,change in [('missing state/effects proof',lambda r:r.update(lean_evidence=r['lean_evidence'][:-1])),('wrong state/effects receipt',lambda r:r['lean_evidence'][-1].update(receipt_sha256='0'*64))]:
 d=copy.deepcopy(edges);root=next(x for x in d['row_certificates'] if x['row']=='TX1:185');change(root)
 try:validate(base,d)
 except (ValueError,AssertionError):results.append(dict(test=label,status='PASS',outcome='rejected'))
 else:raise AssertionError(label)
out,delta=validate(base,edges)
assert len(delta['composed_rows_closed'])==68 and delta['edge_closed']==117
results.append(dict(test='full strengthened packet',status='PASS',outcome='both prefix rows CLOSED'))
(E/'NEV_PREFIX_FRAME_TESTS.json').write_text(json.dumps(dict(passed=len(results),tests=results),indent=2)+'\n');print(json.dumps(dict(passed=len(results))))
