"""Validate retained timing receipts and recompute summaries; no workload launch."""
from pathlib import Path
import json,statistics,math,time
E=Path(__file__).resolve().parent
load=lambda n:json.loads((E/n).read_text())
t=load('measurement/comparison.json');pairs=load('measurement/pairs.json')
clock=load('window-clock.json');clean=load('window-cleanup.json');drain=load('drain-complete.json')
assert clean['removed'] and clean['marker_removal_time']<=clock['until']
assert math.isclose(clock['until']-clock['start'],1500) and clock['never_extended']
assert clock['start']<=drain['utc']<=t['start']<=t['end']<=clean['marker_removal_time']
assert drain['seconds']<=600
assert load('preflight-comparison.json')['passed']
assert len(pairs)==t['completed_pairs'] and t['planned_pairs']==10
assert len(pairs)>=5
for i,p in enumerate(pairs):
 assert p['pair']==i and p['coin']==100+i
 assert p['order']==(['control','candidate'] if i%2==0 else ['candidate','control'])
 before=load(f'measurement/pair-{i}-before.json');after=load(f'measurement/pair-{i}-after.json')
 assert before['package_temperatures_millidegrees'] and after['package_temperatures_millidegrees']
 assert not before['read_errors'] and not after['read_errors']
 delta={k:after['thermal_counters'][k]-v for k,v in before['thermal_counters'].items() if k.endswith(('_count','_total_time_ms'))}
 assert delta==p['thermal_counter_deltas'] and all(v>=0 for v in delta.values())
 assert p['throttled']==any(v>0 for v in delta.values())
 for w in ['control','candidate']:
  for boundary in ['before','after']:
   g=load(f'measurement/pair-{i}-{w}-{boundary}-guard.json');assert g['quiet'] and not g['other_capped_user_jobs']
 for c in p['comparisons']:
  assert c['canonical_result_identical'] and c['ledger_identical'] and all(f['identical'] for f in c['files'].values())
  assert all(r['status']=='Ok' for r in c['records'].values())
for row in t['timing']:
 for name,selected in [('all',pairs),('throttled',[p for p in pairs if p['throttled']]),('unthrottled',[p for p in pairs if not p['throttled']])]:
  g=row['groups'][name]
  for w in ['control','candidate']:
   values=[c['records'][w]['seconds'] for p in selected for c in p['comparisons'] if c['fixture']==row['fixture']]
   s=g['statistics'][w];assert s['n']==len(values)
   if values:
    assert s['seconds']==values and s['median']==statistics.median(values)
    ordered=sorted(values)
    for key,q in [('p10',.1),('p90',.9)]:
     pos=(len(values)-1)*q;lo=int(pos);hi=min(lo+1,len(values)-1)
     assert s[key]==ordered[lo]+(ordered[hi]-ordered[lo])*(pos-lo)
  if selected:assert g['ratio_candidate_control']==g['statistics']['candidate']['median']/g['statistics']['control']['median']
 valid=t['unthrottled_pairs']>=5;g=row['groups']['unthrottled']
 verdict=('PASS' if g['statistics']['candidate']['median']<15 and g['ratio_candidate_control']<=1.10 else 'FAIL') if valid else 'INCOMPLETE'
 assert verdict==row['verdict']
if t['error']:
 assert t['error']=="AssertionError(('foreign capped job', 'pair-7-candidate-after'))"
 g=load('measurement/pair-7-candidate-after-guard.json')
 assert not g['quiet'] and any('pv-b3p6-lean-42574.scope' in x['cgroup'] for x in g['other_capped_user_jobs'])
 assert clock['start']<g['utc']<clock['until']
r=load('measurement-scope/receipt/receipt.json')
assert r['exit_status']==(1 if t['error'] else 0) and r['swaps']==0
assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
assert t['passed']==(t['error'] is None and len(pairs)==10 and all(r['verdict']=='PASS' for r in t['timing']))
(E/'stage-b-validation.json').write_text(json.dumps(dict(passed=True,utc=time.time(),completed_pairs=len(pairs),unthrottled_pairs=t['unthrottled_pairs'],throttled_pairs=t['throttled_pairs'],scope='Independent receipt consistency, quantiles, gates, quiet guards, thermal classification, byte comparisons, timing and caps; no native workload rerun'),indent=2)+'\n')
print('Stage B evidence validated',t['passed'])
