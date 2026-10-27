from pathlib import Path
import json
E=Path('evidence/pv-batch2-20261027');F=json.loads((E/'FINAL.json').read_text())
costs={r['name']:r['microseconds_per_call'] for r in F['function_cost']['rows']}
rows=[]
for fixture in ['transfer','withdrawal']:
 c=json.loads((E/'call-counts'/f'{fixture}.json').read_text())
 counts=c['op_counts_copy_then_original_249_to_253'];parts=[]
 for i,op in enumerate(range(249,254)):
  copy=f'{op}_copy'+('_with_allocation' if op==251 else '')
  delta=costs[copy]-costs[f'{op}_original'];parts.append(dict(op=op,copy_calls=counts[i],original_calls=counts[i+5],delta_us_per_call=delta,projected_delta_us=counts[i]*delta))
 us=sum(p['projected_delta_us'] for p in parts)
 rows.append(dict(fixture=fixture,coin=c['coin'],proof_attempts=c['attempts'],parts=parts,projected_delta_us=us,projected_delta_seconds=us/1e6,percent_of_14_38s=us/1e6/14.38*100,passes=us/1e6<=.02*14.38))
(E/'call-counts/projection.json').write_text(json.dumps(dict(method='Requested sum of observed copy calls times prior inclusive microbenchmark deltas; raw calls nested in materialize are also counted, so inclusive cost overlaps. Finite fixture estimate, not a bound. Instrumented timings are not performance measurements.',threshold_seconds=.2876,rows=rows),indent=2)+'\n')
print(rows[0]['projected_delta_us'])
