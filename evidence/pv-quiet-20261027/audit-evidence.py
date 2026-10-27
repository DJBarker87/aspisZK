from pathlib import Path
import json,math,statistics
H=Path(__file__).resolve().parent
read=lambda p:json.loads((H/p).read_text())
x=read('comparison.json')
assert x['passed'] and x['completed_pairs']==5 and x['error'] is None
assert len(x['samples'])==20 and len(x['comparisons'])==10
for row in x['samples']:
 assert row['status']=='Ok' and row['exit_status']==0 and row['coin']==100+row['pair']
 assert row['order']==(['control','candidate'] if row['pair']%2==0 else ['candidate','control'])
for t in x['timing']:
 for side in ['control','candidate']:
  vals=sorted(t['seconds'][side]);assert len(vals)==5
  assert t['statistics'][side]['median']==statistics.median(vals)
  for p,name in [(0.1,'p10'),(0.9,'p90')]:
   rank=(len(vals)-1)*p;lo=math.floor(rank);hi=math.ceil(rank)
   expected=vals[lo]+(vals[hi]-vals[lo])*(rank-lo)
   assert abs(expected-t['statistics'][side][name])<1e-12
 assert t['statistics']['candidate']['median']<15
 assert t['ratio']==t['statistics']['candidate']['median']/t['statistics']['control']['median']<=1.10
for row in x['comparisons']:
 for f in row['files'].values():assert f['byte_identical'] and f['control_sha256']==f['candidate_sha256'] and f['control_bytes']==f['candidate_bytes']
guards=list((H/'measurement').glob('*-guard.json'));assert len(guards)==20
for p in guards:
 r=json.loads(p.read_text());assert r['quiet'] and not r['other_capped_user_jobs']
for p in ['build-control-2','build-candidate-2','preflight-scope','measurement-scope']:
 r=read(p+'/receipt/receipt.json');assert r['exit_status']==0 and r['swaps']==0
 assert r['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
a=read('window-start.json');b=read('window-end.json')
assert a['marker']['until']==a['start']+3600 and a['start']<b['marker_removed']<a['marker']['until']
assert b['process_exit']==0 and not b['marker_exists']
assert all(not p['exists_after'] for p in read('cleanup.json')['cargo_targets'])
assert read('source-verification.json')['passed']
print('PASS: samples, order, quantiles, ratios, byte receipts, 20 quiet guards, caps, lifecycle, source identity and target cleanup')
