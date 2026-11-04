from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(91,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(92,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('outer_reentry_live_frame','NFI_wrong_reentry_frame'),('inner_cursor_live_frame','NFI_wrong_inner_live_frame'),('tail_decoder_head_frame','NFI_wrong_tail_head_frame'),('wrapper_return_to_caller_frame','NFI_wrong_wrapper_return_frame')]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((93+2*i+j,'fast_dots::NFI_dots::'+h,w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_LIVE_PAYLOAD.json','NFI_KANI_BASE':'NFI_ORIGINAL_BASE.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
