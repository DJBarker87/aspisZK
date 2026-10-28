from pathlib import Path
import subprocess,json
E=Path('evidence/pv-batch2-20261027/batch2f');D='/home/dombarker/project-offloads/codex-pv-batch2-20261027';H='dombarker@100.108.41.90'
for name in ['receipt/receipt.json','receipt/stdout.log','receipt/stderr.log','receipt/time.log','command.json']:
 rel='candidate/batch2f-cost-run-001/'+name;r=subprocess.run(['ssh',H,'cat '+D+'/'+rel],capture_output=True,check=True);p=E/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(r.stdout)
r=json.loads((E/'candidate/batch2f-cost-run-001/receipt/receipt.json').read_text());assert r['exit_status']==0
costs={};data=[]
for line in (E/'candidate/batch2f-cost-run-001/receipt/stdout.log').read_text().splitlines():
 name,n,sec=line.split();us=float(sec)*1e6/int(n);costs[name]=us;data.append(dict(name=name,iterations=int(n),seconds=float(sec),microseconds_per_call=us))
rows=[]
for fixture in ['transfer','withdrawal']:
 c=json.loads((E.parent/'call-counts'/f'{fixture}.json').read_text());counts=c['op_counts_copy_then_original_249_to_253'];parts=[]
 for i,op in enumerate(range(249,254)):
  copy=f'{op}_copy'+('_with_allocation' if op==251 else '');delta=costs[copy]-costs[f'{op}_original'];parts.append(dict(op=op,copy_calls=counts[i],delta_us_per_call=delta,projected_delta_us=counts[i]*delta))
 us=sum(p['projected_delta_us'] for p in parts);rows.append(dict(fixture=fixture,parts=parts,projected_delta_us=us,threshold_seconds=.2876,passes=us/1e6<=.2876))
j=dict(passed=all(r['passes'] for r in rows),scope='Finite inclusive microbenchmark with retained non-inlined Box boundary and caller Vec allocation; indicative estimate, not a latency bound or quiet-window adoption timing gate. Nested raw work overlaps inclusive materialize costs.',source_revision=r['source_revision'],costs=data,projection=rows,receipt='candidate/batch2f-cost-run-001/receipt/receipt.json',call_counts='Reuse unchanged callback counts; Box factory adds no source-op invocation')
(E/'COST-GATE.json').write_text(json.dumps(j,indent=2)+'\n');print([(x['fixture'],x['projected_delta_us'],x['passes']) for x in rows]);assert j['passed']
