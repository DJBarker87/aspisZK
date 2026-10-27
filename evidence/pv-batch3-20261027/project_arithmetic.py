from pathlib import Path
import json,sys
D=Path(__file__).resolve().parent
old=json.loads((D/'arithmetic-dropfree-projection.json').read_text());label=sys.argv[1]
measurements={}
for l in (D/'receipts'/label/'receipt/stdout.log').read_text().splitlines():
 if l.startswith('{"op"'):
  v=json.loads(l);measurements[v['op']]=v
assert len(measurements)==24,len(measurements)
rows=[]
for r in old['projections']:
 r=dict(r);f=r['fixture'];counts=r['mask_prefix_counts']
 delta=sum(n*measurements[f'117-{f}-prefix-{i}']['paired_delta_us'] for i,n in enumerate(counts))
 # 121 source did not change, retain its previous measurement.
 poly=old['measurements'][f'121-{f}']['paired_delta_us']*r['counts_117_121'][1]
 r['cumulative_delta_us']+=delta+poly-r['new_arithmetic_delta_us'];r['new_arithmetic_delta_us']=delta+poly
 r['percent']=100*r['cumulative_delta_us']/14380000;r['within_two_percent']=r['percent']<=2
 rows.append(r)
report=dict(source_revision=(D/'revision').read_text().strip(),measurements=measurements,fixtures=rows,all_pass=all(r['within_two_percent'] for r in rows),unchanged_measurements='retain prior per-op measurements, including121')
(D/(sys.argv[2] if len(sys.argv)>2 else 'mask-split-projection.json')).write_text(json.dumps(report,indent=2)+'\n')
print([(r['fixture'],r['percent']) for r in rows]);sys.exit(0 if report['all_pass'] else 2)
