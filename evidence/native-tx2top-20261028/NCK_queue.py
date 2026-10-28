from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
pairs=[('NCK_kmx::KMX_checks::KMX_ptr_correct',True),
('r1_pool_adapter::NCK_meta::buffer_exact',True),('r1_pool_adapter::NCK_meta::buffer_wrong',False),
('r1_pool_adapter::NCK_meta::account_exact',True),('r1_pool_adapter::NCK_meta::account_wrong',False),
('r1_pool_adapter::NCK_meta::pool_id',True),('r1_pool_adapter::NCK_meta::pool_wrong',False),
('r1_pool_adapter::NCK_meta::registry_id',True),('r1_pool_adapter::NCK_meta::registry_wrong',False),
('NCK_dispatch::admitted_exact',True),('NCK_dispatch::admitted_wrong',False),
('NCK_dispatch::entry_reject',True),('NCK_dispatch::entry_wrong',False)]
for name in ['key','owner','data_error','length_ok','readonly_buffer','checkpoint_meta','stage2_empty','stage2_owned_empty']:
 neg={'length_ok':'length_wrong','checkpoint_meta':'checkpoint_wrong'}.get(name,name+'_wrong')
 pairs += [('r1_pool_adapter::owned::NCK_owned::'+name,True),('r1_pool_adapter::owned::NCK_owned::'+neg,False)]
for i,(h,positive) in enumerate(pairs,3):
 if len(sys.argv)>1 and i<int(sys.argv[1]):continue
 a=f'NCK_K{i:03}'
 assert not (E/a/'receipt.json').exists(),'do not repeat a run'
 r=subprocess.run(['python3',str(E/'NCK_kani.py'),a,'programs/r1-cost-probe',h,str(E/'NCK_native.patch')],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 print(a,h,flush=True);print(r.stdout[-1200:],flush=True)
 if r.returncode!=0:raise SystemExit('STOP own runner error '+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 expected=(rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out) if positive else (rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'Failed Checks:' in out and 'unwinding assertion' not in out)
 with (E/'NCK_GATE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=h,positive=positive,expected_verdict=expected))+'\n')
 if not expected:raise SystemExit('STOP unexpected verdict; inspect, never rerun a timeout unchanged')
