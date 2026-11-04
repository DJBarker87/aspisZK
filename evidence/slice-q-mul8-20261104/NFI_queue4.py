from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(39,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(40,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('main_failure_prefix','NFI_wrong_main_failure'),('tail_failure_prefix','NFI_wrong_tail_failure'),('head_to_tail_frame','NFI_wrong_head_tail'),('main_parser_state_frame','NFI_wrong_main_state'),('tail_parser_state_frame','NFI_wrong_tail_state')]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((41+2*i+j,'NFI_failures::'+h,w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_FAILURE_PAYLOAD.json','NFI_KANI_BASE':'NFI_FAILURE_BASE.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
