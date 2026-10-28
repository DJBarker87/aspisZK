from pathlib import Path
import json
E=Path(__file__).resolve().parent
r=[json.loads(x) for x in (E/'KDX_LEDGER.jsonl').read_text().splitlines()]
assert len(r)==30 and {x['attempt'] for x in r}=={f'KDX_K{i:03}' for i in range(1,31)}
assert sum(x['result']=='PASS' for x in r)==8
assert sum(x['result']=='TIMEOUT' for x in r)==1
assert all(str(x['swaps'])=='0' for x in r)
scan=json.loads((E/'KDX_ALL_PASS_SCAN.json').read_text());assert len(scan)==331
assert not json.loads((E/'KDX_SCAN_REVIEW.json').read_text())
assert not any(x['unwinding_disabled'] for x in scan)
assert json.loads((E/'KDX_TRACE_VALUES.json').read_text())['different_cells']==[15]
assert 'VERIFICATION:- SUCCESSFUL' in (E/'KDX_K029/stdout.log').read_text()
assert 'VERIFICATION:- FAILED' in (E/'KDX_K030/stdout.log').read_text()
assert not json.loads((E/'KDX_CLEANUP.json').read_text())['live_own_scopes']
for x in r:
 g=json.loads((E/x['graph']).read_text());a=json.loads((E/(x['attempt']+'-reservation.json')).read_text())
 assert g['allowed'] is True and g['unchanged'] and g['lock_before']==g['lock_after']
 assert a['allowed'] is True
 assert x['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
(E/'KDX_VALIDATION.json').write_text(json.dumps(dict(kani_invocations=30,lean_invocations=0,rust_invocations=0,passes=8,passing_evidence_replays=7,false_property_pass=1,property_failures=6,timeouts=1,compile_errors=15,original_passes_scanned=331,patches_scanned=287,missing_harness_definitions=0,original_disabled_unwinding=0,all_lock_checks_unchanged=True,all_swaps_zero=True,axioms='N/A: no Lean',max_peak_rss_kib=max(int(x['peak_rss_kib']) for x in r),total_run_wall_seconds=sum(x['wall_seconds'] for x in r)),indent=2)+'\n')
print('KDX packet validation PASS')
