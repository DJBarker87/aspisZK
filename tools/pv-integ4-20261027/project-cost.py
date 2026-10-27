"""Reconcile recorded tables only; never execute timing or invent missing rows."""
from pathlib import Path
import json,hashlib
E=Path('evidence/pv-integ4-20261027')
paths=['evidence/pv-batch2-20261027/call-counts/projection.json','evidence/pv-batch3-20261027/mask-expanded-projection.json']
b2,b3=[json.loads(Path(p).read_text()) for p in paths]
rows=[]
for a,b in zip(b2['rows'],b3['fixtures']):
 assert a['fixture']==b['fixture']
 known=a['projected_delta_us']+b['cumulative_delta_us']
 rows.append(dict(fixture=a['fixture'],batch2_delta_us=a['projected_delta_us'],batch3_delta_us=b['cumulative_delta_us'],known_subtotal_delta_us=known,known_subtotal_seconds=known/1e6,percent_of_14_38s=known/14380000*100,full_cumulative_delta_us=None,missing_terms=['op223','batch1:230,254,258']))
r=dict(method='Sum recorded projections only. Batch3 table is cumulative within batch3: do not sum its successive tables. Batch2 retains inclusive nested-call overlap. Inputs have different coins (batch2 coin100; batch3 coin0). This is a finite mixed-fixture analytical projection, not whole-prover timing or a formal bound.',inputs=[dict(path=p,sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest()) for p in paths],rows=rows,complete=False,missing='No per-call cost tables found in inherited op223/batch1 evidence, route2 packet, or design. Missing values are unknown, never zero. Full op223+batches1–3 sum cannot be established from available recorded tables; no timing run authorized or performed.')
(E/'cost-projection.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(rows,indent=2))
