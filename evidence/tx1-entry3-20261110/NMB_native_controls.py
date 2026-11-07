"""Serial fixed-array interface fidelity; a failed preflight is never a control."""
from NMB_native import *
plan=[(5,58295,'weak_contract','invert',False),(6,58295,'real','normal',True),(7,58295,'unimplied','normal',False),(8,58295,'badframe','normal',False)]
for n,start in [(1880,9),(1768,14)]:
 plan += [(start,n,'weak_contract','normal',True),(start+1,n,'weak_contract','invert',False),(start+2,n,'real','normal',True),(start+3,n,'unimplied','normal',False),(start+4,n,'badframe','normal',False)]
for num,n,kind,mode,expected in plan:
 a=f'NMB_K{num:03d}';target=f'NMB_input_{kind}_{n}'
 r=native(a,mode=='invert',target)
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 bad=any(s in log for s in ['CBMC timed out','unwinding failures','could not compile','unsupported operation'])
 verdict=('VERIFICATION:- SUCCESSFUL' in log and r['exit_status']==0)if expected else('VERIFICATION:- FAILED'in log and r['exit_status']==1 and 'Failed Checks:'in log and not bad)
 row=dict(attempt=a,extent=n,kind=kind,mode=mode,expected_pass=expected,exit_status=r['exit_status'],candidate_expected_verdict=verdict,semantic_review_required=not expected)
 with(E/'NMB_INPUT_CONTROLS.jsonl').open('a')as f:f.write(json.dumps(row)+'\n')
 if not verdict:raise RuntimeError('STOP input interface: missing expected semantic verdict '+a)
