from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
jobs=[(35,'NFM_copy::KMX_checks::KMX_ptr_correct',None),(36,'NFM_copy::KMX_checks::KMX_ptr_wrong',None),(37,'fast_dots::NFM_dots::wrapper_original_opening',None),(38,'fast_dots::NFM_dots::wrapper_original_opening','NFM_wrong_original_wrapper')]
for i,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':'NFM_WRAPPER_PAYLOAD.json'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 negative=wrong or h.endswith('_wrong');expected='VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
