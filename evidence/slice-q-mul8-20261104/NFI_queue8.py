from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(77,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(78,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('NFI_original::original_allocation_disjoint_receiver','NFI_wrong_original_disjoint')]
windows += [('fast_pairing::canonical::NFI_pairing::'+n,c) for n,c in [('public_count_reject_frame','NFI_wrong_count_reject'),('public_scalar_reject_frame','NFI_wrong_scalar_reject'),('public_half0_raw_arguments','NFI_wrong_half0_raw_arguments'),('public_half1_raw_arguments','NFI_wrong_half1_raw_arguments'),('final_carrier_input_frame','NFI_wrong_final_input_frame')]]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((79+2*i+j,h,w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_CONTEXT_PAYLOAD.json','NFI_KANI_BASE':'NFI_ORIGINAL_BASE.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
