"""Replace only affected op measurements in the cumulative fixture projection."""
from pathlib import Path
import json
D=Path(__file__).resolve().parent
p=D/'receipts/batch3b-forest-bench-01/receipt/stdout.log'
rows=[json.loads(s) for s in p.read_text().splitlines() if s.startswith('{')];m={r['op']:r for r in rows if 'op' in r}
assert all(k in m for k in ['132','133','228','224-transfer','224-withdrawal'])
base=json.loads((D/'mask-expanded-projection.json').read_text())
f=json.loads((D/'forest-cost-projection.json').read_text())['measurements'];g=json.loads((D/'group2-cost-projection.json').read_text())['measurements']
fixtures=[]
for b in base['fixtures']:
 tag=b['fixture'];replace=2*f['132']['paired_delta_us']+3*f['133']['paired_delta_us']+f['228']['paired_delta_us']+g['224-'+tag]['paired_delta_us']
 new=2*m['132']['paired_delta_us']+3*m['133']['paired_delta_us']+m['228']['paired_delta_us']+m['224-'+tag]['paired_delta_us']
 delta=b['cumulative_delta_us']-replace+new
 fixtures.append(dict(fixture=tag,prior_delta_us=b['cumulative_delta_us'],replaced_delta_us=replace,new_delta_us=new,cumulative_delta_us=delta,percent=delta/143800,within_two_percent=delta<=287600))
out=dict(kind='paired microbenchmark fixture projection; no whole-prover timing or formal bound',source_revision='fffdafc2d4',measurements=m,fixtures=fixtures,all_pass=all(x['within_two_percent']for x in fixtures),unchanged_measurements='retained mask-expanded projection inputs')
(D/'batch3b-forest-projection.json').write_text(json.dumps(out,indent=1)+'\n');print(json.dumps(fixtures));assert out['all_pass'],'STOP: cumulative cost exceeds +2%'
