from pathlib import Path
import os,subprocess,sys
E=Path(__file__).resolve().parent
jobs=[(4,'NFI_copy::KMX_checks::KMX_ptr_correct',None,'NFI_FRAME_PAYLOAD.json'),(5,'NFI_copy::KMX_checks::KMX_ptr_wrong',None,'NFI_FRAME_PAYLOAD.json')]
for i,(h,c) in enumerate([('entry_to_inner_frame','NFI_wrong_entry'),('cursor_to_product_frame','NFI_wrong_cursor_product'),('exhausted_inner_to_fold_frame','NFI_wrong_exhaust_fold'),('fold_to_next_outer_frame','NFI_wrong_fold_next')]):
 for j,w in enumerate([None,c]):jobs.append((6+2*i+j,'fast_dots::NFI_dots::'+h,w,'NFI_FRAME_PAYLOAD.json'))
for i,h,wrong,payload in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':payload}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
