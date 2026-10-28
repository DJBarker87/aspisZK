from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
pairs=[]
for prefix,names in [('NCK_entry_split',['empty']),('r1_pool_adapter::NCK_adapter_split',['process_empty','scan_short']),('r1_pool_adapter::owned::NCK_snapshot_split',['rejected_length','borrow_conflict','header_reject','owned_header_reject'])]:
 for n in names:
  neg={'header_reject':'header_wrong','owned_header_reject':'owned_header_wrong'}.get(n,n+'_wrong')
  pairs.extend([('programs/r1-cost-probe',prefix+'::'+n,True),('programs/r1-cost-probe',prefix+'::'+neg,False)])
for n in ['bad_magic','bad_variant']:
 pairs.extend([('crates/aspis-r1-cost-probe','verifier::candidate::NCK_shape::'+n,True),('crates/aspis-r1-cost-probe','verifier::candidate::NCK_shape::'+n+'_wrong',False)])
# Recalibrate the SAME previously failing entry control after cfg-source changes.
# Known Kani fidelity sensitivity makes this a specific changed-input question.
pairs.append(('programs/r1-cost-probe','NCK_dispatch::entry_wrong',False))
assert len(pairs)==19
for i,(crate,h,positive) in enumerate(pairs,32):
 if len(sys.argv)>1 and i<int(sys.argv[1]):continue
 a=f'NCK_K{i:03}';assert not (E/a/'receipt.json').exists()
 r=subprocess.run(['python3',str(E/'NCK_kani.py'),a,crate,h,str(E/'NCK_split.patch')],capture_output=True,text=True)
 (E/(a+'-driver.log')).write_text(r.stdout+r.stderr)
 print(a,h,r.stdout[-650:],flush=True)
 if r.returncode!=0:raise SystemExit('STOP own runner error '+r.stderr)
 rc=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text()
 expected=(rc['exit_status']==0 and 'VERIFICATION:- SUCCESSFUL' in out) if positive else (rc['exit_status']!=0 and 'VERIFICATION:- FAILED' in out and 'Failed Checks:' in out and 'unwinding assertion' not in out)
 with (E/'NCK_GATE_RESULTS.jsonl').open('a') as f:f.write(json.dumps(dict(attempt=a,harness=h,positive=positive,expected_verdict=expected))+'\n')
 if not expected:raise SystemExit('STOP unexpected verdict; inspect before moving to independent member')
