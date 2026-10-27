"""Summarize finite original-vs-copy samples and observed fixture call counts."""
from pathlib import Path
import json,statistics,hashlib
E=Path('evidence/pv-integ4-20261027');rows=[];round_id=None
for line in (E/'batch1-cost-run/receipt/stdout.log').read_text().splitlines():
 if line.startswith('ROUND '):round_id=int(line.split()[1]);continue
 name,n,s=line.split();rows.append(dict(round=round_id,name=name,iterations=int(n),wall_seconds=float(s),microseconds_per_call=float(s)*1e6/int(n)))
assert len(rows)==30
parts=[]
for op in [230,254,258]:
 old=[r for r in rows if r['name']==f'{op}_original'];new=[r for r in rows if r['name']==f'{op}_copy']
 ds=[b['microseconds_per_call']-a['microseconds_per_call'] for a,b in zip(old,new)]
 parts.append(dict(op=op,original_median_us=statistics.median(r['microseconds_per_call'] for r in old),copy_median_us=statistics.median(r['microseconds_per_call'] for r in new),paired_delta_us=ds,delta_us_per_call=statistics.median(ds)))
fixtures=[]
for fixture in ['transfer','withdrawal']:
 record=json.loads((E/f'batch1-counts/fixtures/{fixture}-0/result.json').read_text());counts=record['batch1_counts_230_254_258'];assert record['status']=='Ok'
 previous=json.loads((E/'fixture-comparison.json').read_text())
 fs=[]
 for p,n in zip(parts,counts):fs.append(dict(**p,copy_calls=n,projected_delta_us=n*p['delta_us_per_call']))
 us=sum(p['projected_delta_us'] for p in fs)
 fixtures.append(dict(fixture=fixture,coin=record['coin'],attempts=record['attempts'],parts=fs,projected_delta_us=us,projected_delta_seconds=us/1e6))
r=dict(method='Five ordered original/copy rounds on fixed public-shaped inputs; per-op median of paired per-call deltas times observed copy calls in the complete coin0 fixture prover call. Counter observations stop before verifier execution. Timings from instrumented fixture runs are not performance measurements. Finite estimate, not a cost bound or a quiet-window gate.',samples=rows,per_call=parts,fixtures=fixtures)
(E/'batch1-projection.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(fixtures,indent=2))
