"""Validate retained D358 receipts without executing a prover."""
from pathlib import Path
import json,math,statistics,hashlib
R=Path(__file__).resolve().parent
read=lambda p:json.loads((R/p).read_text())
pre=read('preflight.json');clock=read('window-clock.json');drain=read('drain-complete.json');summary=read('measurement/comparison.json');pairs=read('measurement/pairs.json');removed=read('measurement-marker-removal.json');receipt=read('measurement-scope/receipt/receipt.json')
assert pre['scanner_sha256']=='662a42781e004635a4a0bde760a90082834834aa63bb15a3062ea0aef490542d'
assert not pre['rebuild'] and not pre['stage_a_repeated']
assert pre['utc']<=clock['start']<drain['utc']<=summary['start']<=summary['end']<=clock['until']
assert clock['until']-clock['start']==1500 and clock['never_extended']
assert drain['seconds']<=600.1
assert removed['removed'] and summary['end']<=removed['marker_removal_time']<clock['until']
assert receipt['exit_status']==0 and receipt['swaps']==0
assert receipt['limits']=={'memory.high':str(6*2**30),'memory.max':str(8*2**30),'memory.swap.max':'0','pids.max':'64'}
audit=read('post-window-audit.json')
assert not audit['marker_exists'] and all(not t['exists'] for t in audit['targets'])
for name,digest in audit['script_sha256'].items():assert hashlib.sha256((R/name).read_bytes()).hexdigest()==digest
consecutive=0;guards=0
for i,p in enumerate(pairs):
 assert p['pair']==i and p['coin']==100+i
 assert p['order']==(['control','candidate'] if i%2==0 else ['candidate','control'])
 before=read(f'measurement/pair-{i}-before.json');after=read(f'measurement/pair-{i}-after.json')
 assert before['affinity']==after['affinity']=='0-21'
 assert before['package_temperatures_millidegrees'] and after['package_temperatures_millidegrees'] and not before['read_errors'] and not after['read_errors']
 delta={k:after['thermal_counters'][k]-v for k,v in before['thermal_counters'].items() if k.endswith(('_count','_total_time_ms'))}
 assert delta==p['thermal_counter_deltas'] and all(v>=0 for v in delta.values())
 assert p['throttled']==any(v>0 for v in delta.values())
 gs=[read(f'measurement/pair-{i}{suffix}-guard.json') for suffix in ['-before','-control-before','-control-after','-candidate-before','-candidate-after']]
 guards+=len(gs)
 for g in gs: assert g['quiet']==(not g['other_capped_user_jobs'] and not g['foreign_cx_pv_scopes'])
 assert p['valid']==all(g['quiet'] for g in gs)
 consecutive=0 if p['valid'] else consecutive+1
 if consecutive>=3:assert i==len(pairs)-1 and summary['stop_reason']=='three consecutive invalid pairs'
 for c in p['comparisons']:
  assert c['canonical_result_identical'] and c['ledger_identical']
  assert all(v['identical'] and v['candidate']==v['control'] for v in c['files'].values())
  assert c['canonical_records']['control']==c['canonical_records']['candidate']
  assert c['ledger_manifest']['control']==c['ledger_manifest']['candidate']
  assert all(r['status']=='Ok' for r in c['records'].values())
assert summary['completed_pairs']==len(pairs)
assert summary['valid_pairs']==sum(p['valid'] for p in pairs)
assert summary['invalid_pairs']==sum(not p['valid'] for p in pairs)
assert summary['valid_unthrottled_pairs']==sum(p['valid'] and not p['throttled'] for p in pairs)
assert summary['planned_pairs']==summary['minimum_unthrottled_pairs']==10
for row in summary['timing']:
 for group,predicate in [('all',lambda p:True),('valid_unthrottled',lambda p:p['valid'] and not p['throttled']),('valid_throttled',lambda p:p['valid'] and p['throttled']),('invalid',lambda p:not p['valid'])]:
  s=row['groups'][group]['statistics']
  for who in ['control','candidate']:
   v=[c['records'][who]['seconds'] for p in pairs if predicate(p) for c in p['comparisons'] if c['fixture']==row['fixture']]
   assert s[who]['n']==len(v)
   if v:
    assert math.isclose(s[who]['median'],statistics.median(v),rel_tol=1e-12)
    v=sorted(v)
    for label,q in [('p10',.1),('p90',.9)]:
     pos=(len(v)-1)*q;lo=int(pos);hi=min(lo+1,len(v)-1)
     assert math.isclose(s[who][label],v[lo]+(v[hi]-v[lo])*(pos-lo),rel_tol=1e-12)
  ratio=row['groups'][group]['ratio_candidate_control']
  if s['candidate']['n']:assert math.isclose(ratio,s['candidate']['median']/s['control']['median'],rel_tol=1e-12)
  else:assert ratio is None
 enough=summary['valid_unthrottled_pairs']==10
 g=row['groups']['valid_unthrottled']
 verdict='UNDECIDED' if not enough else ('PASS' if g['statistics']['candidate']['median']<15 and g['ratio_candidate_control']<=1.10 else 'FAIL')
 assert row['verdict']==verdict
out=dict(validated=True,pairs=len(pairs),guard_snapshots=guards,valid_unthrottled_pairs=summary['valid_unthrottled_pairs'],marker_removal_delay_seconds=removed['marker_removal_time']-summary['end'],no_prover_execution=True)
(R/'validation.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
