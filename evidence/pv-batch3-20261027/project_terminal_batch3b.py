from pathlib import Path
import json
D=Path(__file__).resolve().parent
p=D/'receipts/batch3b-terminal-bench-01/receipt/stdout.log'
rows=[json.loads(s) for s in p.read_text().splitlines() if s.startswith('{')];m={r['op']:r for r in rows if 'op'in r}
assert all(f'227-{tag}-prefix-{i}' in m for tag in ['transfer','withdrawal']for i in range(11))
base=json.loads((D/'batch3b-owned-projection.json').read_text());old=json.loads((D/'group3-cost-projection.json').read_text());fixtures=[]
for b in base['fixtures']:
 tag=b['fixture'];prior=next(x for x in old['projections']if x['fixture']==tag)
 delta227=sum(n*m[f'227-{tag}-prefix-{i}']['paired_delta_us']for i,n in enumerate(prior['terminal_prefix_counts']))
 delta=b['cumulative_delta_us']-prior['terminal_delta_us']+delta227
 fixtures.append(dict(fixture=tag,prior_cumulative_us=b['cumulative_delta_us'],replaced_terminal_us=prior['terminal_delta_us'],new_terminal_us=delta227,cumulative_delta_us=delta,percent=delta/143800,within_two_percent=delta<=287600))
out=dict(source_revision='dcbd4adbf8',kind='paired fixture projection; no whole-prover timing or formal cost bound',measurements=m,fixtures=fixtures,all_pass=all(x['within_two_percent']for x in fixtures),unchanged='retain every other measurement from owned stage')
(D/'batch3b-terminal-projection.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(fixtures));assert out['all_pass'],'STOP: cumulative cost exceeds +2%'
