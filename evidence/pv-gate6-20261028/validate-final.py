"""Validate final receipt consistency and independently recompute timing stats."""
from pathlib import Path
import json, math, statistics, hashlib, time
E=Path(__file__).resolve().parent
load=lambda p:json.loads((E/p).read_text())
assert load('stage-a-validation.json')['passed']
assert load('preflight-comparison.json')['passed']
t=load('measurement/comparison.json');pairs=load('measurement/pairs.json')
assert len(pairs)==t['completed_pairs']==7 and t['planned_pairs']==10
assert t['unthrottled_pairs']==0 and t['throttled_pairs']==7 and not t['passed']
assert t['error']=="AssertionError(('foreign capped job', 'pair-7-candidate-after'))"
for i,p in enumerate(pairs):
    assert p['pair']==i and p['coin']==100+i
    assert p['order']==(['control','candidate'] if i%2==0 else ['candidate','control'])
    assert p['throttled'] and any(v>0 for v in p['thermal_counter_deltas'].values())
    for side in ['control','candidate']:
        for where in ['before','after']:
            assert load(f'measurement/pair-{i}-{side}-{where}-guard.json')['quiet']
    for c in p['comparisons']:
        assert c['canonical_result_identical'] and c['ledger_identical']
        assert all(f['identical'] for f in c['files'].values())
        assert all(r['status']=='Ok' for r in c['records'].values())
for row in t['timing']:
    assert row['verdict']=='INCOMPLETE'
    for side in ['control','candidate']:
        values=[c['records'][side]['seconds'] for p in pairs for c in p['comparisons'] if c['fixture']==row['fixture']]
        s=sorted(values)
        quant=lambda q:s[int((len(s)-1)*q)]+(s[math.ceil((len(s)-1)*q)]-s[int((len(s)-1)*q)])*((len(s)-1)*q-int((len(s)-1)*q))
        for group in ['all','throttled']:
            z=row['groups'][group]['statistics'][side]
            assert z['n']==7 and z['seconds']==values
            for key,value in [('median',statistics.median(values)),('p10',quant(.1)),('p90',quant(.9))]:assert math.isclose(z[key],value,rel_tol=1e-12)
    g=row['groups']['all'];assert math.isclose(g['ratio_candidate_control'],g['statistics']['candidate']['median']/g['statistics']['control']['median'],rel_tol=1e-12)
clock=load('window-clock.json');clean=load('window-cleanup.json')
assert math.isclose(clock['until']-clock['start'],1500) and clock['never_extended']
assert clean['removed'] and t['end']<=clean['marker_removal_time']<clock['until']
assert clean['marker_removal_time']-t['end']<1
assert load('drain-complete.json')['seconds']<600
foreign=load('measurement/pair-7-candidate-after-guard.json')
assert not foreign['quiet'] and any('pv-b3p6-lean-42574.scope' in x['cgroup'] for x in foreign['other_capped_user_jobs'])
receipts=[]
for p in sorted(E.rglob('receipt/receipt.json')):
    r=json.loads(p.read_text());is_measurement=str(p.relative_to(E)).startswith('measurement-scope/')
    assert r['exit_status']==(1 if is_measurement else 0) and r['swaps']==0
    assert r['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
    assert 'N/A' in r['print_axioms']
    receipts.append(dict(path=str(p.relative_to(E)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),exit=r['exit_status']))
assert len(receipts)==14
assert all(x.get('deleted') or x.get('existed') is False for x in load('cleanup.json')['targets'])
(E/'final-validation.json').write_text(json.dumps(dict(utc=time.time(),passed=True,scope='Receipt consistency, independent timing recomputation, retained partial-run classification; no workload rerun',charged_native_attempts=14,receipts=receipts,stage_a='PASS',stage_b='INCOMPLETE: foreign capped job; 0 unthrottled pairs',target_established=False),indent=2)+'\n')
print('Final evidence verified: Stage A PASS; Stage B INCOMPLETE; 14 launched scopes, no reruns')
