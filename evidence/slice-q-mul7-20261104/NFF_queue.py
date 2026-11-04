from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(3,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_PAYLOAD.json'),(4,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_PAYLOAD.json'),(5,'fast_dots::NFF_dots::outer_fold_window',None,'NFF_NEXT_PAYLOAD.json'),(6,'fast_dots::NFF_dots::outer_fold_window','NFF_wrong_fold','NFF_NEXT_PAYLOAD.json'),(7,'fast_dots::NFF_dots::wrapper_calls_window',None,'NFF_NEXT_PAYLOAD.json'),(8,'fast_dots::NFF_dots::wrapper_calls_window','NFF_wrong_wrapper','NFF_NEXT_PAYLOAD.json'),(9,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_NEXT_PAYLOAD.json'),(10,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_NEXT_PAYLOAD.json')]
for i,h,wrong,payload in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':payload}
 if wrong:env['NFF_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
