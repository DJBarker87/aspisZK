from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(6,'window_0','NFM_wrong_window_0')]
for cut in range(1,7):jobs += [(5+2*cut,f'window_{cut}',None),(6+2*cut,f'window_{cut}',f'NFM_wrong_window_{cut}')]
for i,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':'NFM_WINDOW_PAYLOAD.json'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:
  r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani','fast_dots::NFM_dots::'+h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 expected='VERIFICATION:- FAILED' if wrong else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
