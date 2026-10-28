from pathlib import Path
import json
D=Path(__file__).resolve().parent
p=D/'receipts/batch3b-fixed-bench-01/receipt/stdout.log'
m={x['op']:x for s in p.read_text().splitlines() if s.startswith('{')and 'op'in(x:=json.loads(s))}
assert all(k in m for k in ['132','133','228','224-transfer','224-withdrawal','226-transfer','226-withdrawal']+[f'227-{tag}-prefix-{i}'for tag in ['transfer','withdrawal']for i in range(11)])
base=json.loads((D/'batch3b-carrier-projection.json').read_text());old=base['measurements'];counts=json.loads((D/'group3-cost-projection.json').read_text())['projections'];fixtures=[]
for b in base['fixtures']:
 tag=b['fixture'];c=next(x for x in counts if x['fixture']==tag)['terminal_prefix_counts']
 prior=2*old['132']['paired_delta_us']+3*old['133']['paired_delta_us']+old['228']['paired_delta_us']+old['224-'+tag]['paired_delta_us']+2*old['226-'+tag]['paired_delta_us']+b['new_terminal_us']
 terminal=sum(n*m[f'227-{tag}-prefix-{i}']['paired_delta_us']for i,n in enumerate(c))
 new=2*m['132']['paired_delta_us']+3*m['133']['paired_delta_us']+m['228']['paired_delta_us']+m['224-'+tag]['paired_delta_us']+2*m['226-'+tag]['paired_delta_us']+terminal
 delta=b['cumulative_delta_us']-prior+new
 fixtures.append(dict(fixture=tag,prior_cumulative_us=b['cumulative_delta_us'],replaced_delta_us=prior,new_delta_us=new,new_terminal_us=terminal,cumulative_delta_us=delta,percent=delta/143800,within_two_percent=delta<=287600))
out=dict(source_revision='c97270adc2b3653dbc7ce65a1b8811722f3c2088',kind='paired fixture projection, not whole-prover timing or formal bound',measurements=m,fixtures=fixtures,all_pass=all(x['within_two_percent']for x in fixtures),unchanged='retain117,121,134 and222 measurements')
(D/'batch3b-fixed-projection.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(fixtures));assert out['all_pass'],'STOP: cumulative cost exceeds +2%'
