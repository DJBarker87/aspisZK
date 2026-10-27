"""Check complete accounting, retained failed evidence and final audit coverage."""
from pathlib import Path
import json,re,hashlib,subprocess
r=Path(__file__).resolve().parents[2];e=r/'evidence/pv-join-20261026/resume4'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
xs=[json.loads(f.read_text()) for f in sorted(e.glob('*-receipt.json'))]
assert len(xs)==5 and [x['attempt'] for x in xs]==list(range(36800,36805))
for x in xs:
 a=x['attempt'];assert sha(e/f'{a}.lean.txt')==x['source_sha256']
 raw=(e/f'{a}-out.log').read_text()
 if x['validation_exit']==0:
  assert 'sorryAx' not in raw and 'error:' not in raw
  for s in x['print_axioms']:
   if 'depends on axioms: [' in s:
    assert set(y.strip() for y in s.split('depends on axioms: [')[1].split(']')[0].split(',')) <= {'propext','Classical.choice','Quot.sound'}
assert all(x['validation_exit']==0 and 'Audit' in x['module'] for x in xs[-3:])
manifest=json.loads((e/'combined-audit-manifest.json').read_text());last=xs[-1]
assert len(manifest['theorems'])==127 and len(last['print_axioms'])==128
raw=(e/'36804-out.log').read_text()
for n in manifest['theorems']+[manifest['headline']]:assert "'"+n+"' " in raw,n
for x in manifest['sources']:
 p=r/'docs/research/v8-r0-zk-20261009/lean'/(x['module'].replace('.','/')+'.lean');assert sha(p)==x['sha256']
native=[dict(directory=str(p.parent.relative_to(e)),**json.loads(p.read_text())) for p in sorted(e.glob('*/receipt.json'))];kani=[x for x in native if x['kind']=='kani'];assert len(kani)==6
assert sorted(x['exit'] for x in kani)==[0,0,0,1,1,124]
t=json.loads((e/'attempt-tally.json').read_text());assert t['ids']==list(range(36800,36805)) and t['charged']==5;t.update(final_audit_remaining=0,unused_lean_budget=95,stopped_on_checked_ROW_counterexample=True,next_unused_id=36805,kani_used=6,kani_remaining=0);(e/'attempt-tally.json').write_text(json.dumps(t,indent=2)+'\n')
summary=dict(branch='codex/pv-join-20261026',base='1ad24470b8',stop='checked counterexample to proposed unrestricted op121 P6 Horner-reference ROW; no source fix or canonical-input premise',lean_attempts=5,lean_budget=100,unused_lean_budget=95,ids=t['ids'],next_unused_id=36805,last_three_are_audits=True,kani_runs=6,kani_passed=3,kani_arithmetic_failure_reports=2,kani_timeouts=1,local_lean_compiles=0,final_attempt=36804,final_exit=0,final_theorem_reports=128,final_source_revision=last['source_revision'],inventory_before=30,inventory_after=30,new_source_laws=0,unreachable_both_fixtures=[],native_deferred=[4,32,122,123,232,257],fixture_reached_sets=None,fixture_byte_equations='both open; concrete rw20 model instance unavailable',endpoint_premises_removed=0,endpoint_premises_changed=0,target_established=False,release_manifest_replayed=False,peak_lean_rss_kib=max(x['peak_rss_kib'] for x in xs),max_completed_native_time_rss_kib=max(x['peak_rss_kib'] or 0 for x in native),timed_out_scan_peak_rss_kib=None,timed_out_scan_child_rss_lower_bound_kib=3445352,swaps=max([x['swaps'] for x in xs]+[x['swaps'] or 0 for x in native]))
(e/'receipt-index.json').write_text(json.dumps(dict(summary=summary,lean_receipts=xs,native_receipts=native),indent=2)+'\n')
(e/'commits.txt').write_text(subprocess.check_output(['git','log','--oneline','1ad24470b8..HEAD'],text=True))
print(json.dumps(summary,indent=2))
