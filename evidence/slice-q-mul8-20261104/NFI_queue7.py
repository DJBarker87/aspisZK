from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(65,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(66,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[(f'wrapper_slot{i}_installation',f'NFI_wrong_wrapper_slot{i}') for i in range(4)]+[('wrapper_prefix_failure','NFI_wrong_wrapper_prefix')]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((67+2*i+j,'fast_dots::NFI_dots::'+h,w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_WRAPPER_PAYLOAD.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
