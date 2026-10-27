"""Add recorded op223 whole-prover deltas and finite batch1/2/3 projections."""
from pathlib import Path
import json,hashlib
E=Path('evidence/pv-integ4-20261027')
paths=['evidence/pv-quiet-20261027/comparison.json',str(E/'batch1-projection.json'),'evidence/pv-batch2-20261027/call-counts/projection.json','evidence/pv-batch3-20261027/mask-expanded-projection.json']
op,b1,b2,b3=[json.loads(Path(p).read_text()) for p in paths];rows=[]
for t,a,b,c in zip(op['timing'],b1['fixtures'],b2['rows'],b3['fixtures']):
 assert t['fixture']==a['fixture']==b['fixture']==c['fixture']
 old=t['statistics']['control']['median'];new=t['statistics']['candidate']['median'];d=new-old
 total=d+(a['projected_delta_us']+b['projected_delta_us']+c['cumulative_delta_us'])/1e6
 rows.append(dict(fixture=t['fixture'],op223_control_median_seconds=old,op223_candidate_median_seconds=new,op223_ratio=t['ratio'],op223_measured_delta_seconds=d,batch1_delta_seconds=a['projected_delta_seconds'],batch2_delta_seconds=b['projected_delta_us']/1e6,batch3_delta_seconds=c['cumulative_delta_us']/1e6,cumulative_delta_seconds=total,percent_of_14_38s=total/14.38*100,projected_seconds_from_14_38=14.38+total))
r=dict(complete=True,method='Add op223 recorded whole-prover median differences (D286/D289 receipt) and batches1/2/3 observed-call projections. Batch3 final table is already cumulative within batch3. Batch2 retains inclusive materialize/raw overlap. Inputs mix op223 coins100–104, batch1/3 coin0 and batch2 coin100. This is a finite mixed-fixture projection, not independent whole-prover timing, a worst-case/formal cost bound, or the merged-candidate quiet timing gate.',inputs=[dict(path=p,sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest()) for p in paths],rows=rows)
(E/'cost-projection.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(rows,indent=2))
