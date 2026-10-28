from pathlib import Path
import json
D=Path(__file__).resolve().parent
r=D/'receipts/batch3b-owned-bench-01/receipt/stdout.log'
rows=[json.loads(s) for s in r.read_text().splitlines() if s.startswith('{')];m={r['op']:r for r in rows if 'op'in r}
assert all(k in m for k in ['132','133','228','224-transfer','224-withdrawal','226-transfer','226-withdrawal']+[f'222-prefix-{i}'for i in range(11)])
base=json.loads((D/'mask-expanded-projection.json').read_text());f=json.loads((D/'forest-cost-projection.json').read_text())['measurements'];g=json.loads((D/'group2-cost-projection.json').read_text());p=json.loads((D/'group3-cost-projection.json').read_text())
fixtures=[]
for b in base['fixtures']:
 tag=b['fixture'];oldg=next(x for x in g['projections']if x['fixture']==tag);oldp=next(x for x in p['projections']if x['fixture']==tag)
 old=2*f['132']['paired_delta_us']+3*f['133']['paired_delta_us']+f['228']['paired_delta_us']+g['measurements']['224-'+tag]['paired_delta_us']+oldg['mle_delta_us']+oldp['public_delta_us']
 mle=sum(n*m[f'222-prefix-{i}']['paired_delta_us']for i,n in enumerate(oldg['prefix_counts']))
 new=2*m['132']['paired_delta_us']+3*m['133']['paired_delta_us']+m['228']['paired_delta_us']+m['224-'+tag]['paired_delta_us']+mle+2*m['226-'+tag]['paired_delta_us']
 delta=b['cumulative_delta_us']-old+new
 fixtures.append(dict(fixture=tag,prior_delta_us=b['cumulative_delta_us'],replaced_delta_us=old,new_delta_us=new,new_mle_delta_us=mle,cumulative_delta_us=delta,percent=delta/143800,within_two_percent=delta<=287600))
out=dict(source_revision='7a5f83b900485a4ab70d63e83fba69e6c0bbb385',kind='paired per-call fixture projection, not whole-prover timing or formal bound',measurements=m,fixtures=fixtures,all_pass=all(x['within_two_percent']for x in fixtures),unchanged='117,121,134,227 measurements retained')
(D/'batch3b-owned-projection.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(fixtures));assert out['all_pass'],'STOP: cumulative cost exceeds +2%'
