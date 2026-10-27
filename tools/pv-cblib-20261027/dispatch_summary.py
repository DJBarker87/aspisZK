from pathlib import Path
import json
root=Path(__file__).resolve().parents[2];out=root/'evidence/pv-cblib-20261027'
def result(name):return next(json.loads(s) for s in (out/name/'output.log').read_text().splitlines() if s.startswith('{'))
a=result('dispatch-auto-calls');s=result('dispatch-soft-calls');c=json.loads((out/'dispatch-census.json').read_text())
assert not a['force_soft'] and s['force_soft']
assert all(a[k] for k in ['sha_detected','sse2','ssse3','sse4.1'])
aa={r['shape']:r for r in a['rows']};ss={r['shape']:r for r in s['rows']};rows=[];auto=soft=0
for shape,n in c['parts_length_histogram'].items():
 assert aa[shape]['digest']==ss[shape]['digest']
 x=aa[shape]['ns_per_call_median'];y=ss[shape]['ns_per_call_median'];auto+=n*x/1e9;soft+=n*y/1e9
 rows.append(dict(shape=shape,calls=n,bytes=aa[shape]['length'],auto_ns=x,soft_ns=y,ratio=y/x,projected_delta_seconds=n*(y-x)/1e9))
rows.sort(key=lambda r:r['projected_delta_seconds'],reverse=True)
delta=soft-auto
optimistic=sum(n*(min(ss[k]['ns_per_call_samples'])-max(aa[k]['ns_per_call_samples']))/1e9 for k,n in c['parts_length_histogram'].items())
pessimistic=sum(n*(max(ss[k]['ns_per_call_samples'])-min(aa[k]['ns_per_call_samples']))/1e9 for k,n in c['parts_length_histogram'].items())
r=dict(fixture_callback_calls=c['sha_callback_calls'],production_attempt_callback_calls_inferred=c['sha_callback_calls']-3,production_attempt_total_sha_calls_inferred=c['sha_callback_calls']-2,production_correction='subtract three fixture_secret hashes; add one durable reservation_path SHA; steady admitted S2 transfer attempt, not retries/setup/verifier. No production census is claimed.',auto_projected_sha_seconds=auto,soft_projected_sha_seconds=soft,weighted_soft_to_auto_ratio=soft/auto,projected_delta_seconds=delta,sample_extreme_sensitivity_seconds=[optimistic,pessimistic],sensitivity_note='Weighted extrema across recorded samples, not a confidence interval or a timing gate.',projections=[dict(historical_baseline_seconds=t,projected_soft_seconds=t+delta,slowdown_percent=100*delta/t,absolute15_estimate=t+delta<15,relative110_estimate=delta<=t*.10) for t in (13.63,13.98)],rows=rows,interpretation='Fixture census plus seven-sample per-shape release microbench medians on shared host, not end-to-end timing or a cost proof. Historical D172 baselines are comparison points, not a same-session control; adoption gate remains open. Small fixture/ledger correction not separately benchmarked.')
(out/'dispatch-projection.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({k:v for k,v in r.items() if k!='rows'},indent=2));print('dominant',rows[:5])
