from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
jobs=[(19,'NFM_copy::KMX_checks::KMX_ptr_correct',None),(20,'NFM_copy::KMX_checks::KMX_ptr_wrong',None)]
for cut in range(7):
 jobs += [(21+2*cut,f'fast_dots::NFM_dots::reject_{cut}',None),(22+2*cut,f'fast_dots::NFM_dots::reject_{cut}',f'NFM_wrong_reject_{cut}')]
for i,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':'NFM_REJECT_PAYLOAD.json'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 negative=wrong or h.endswith('_wrong');expected='VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
