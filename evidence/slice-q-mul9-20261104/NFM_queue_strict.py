from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
jobs=[(39,'NFM_copy::KMX_checks::KMX_ptr_correct',None),(40,'NFM_copy::KMX_checks::KMX_ptr_wrong',None)]
for cut in range(7):
 h=f'fast_dots::NFM_dots::window_{cut}';jobs.append((41+8*cut,h,None))
 for offset,flag in enumerate(['NFM_wrong_left','NFM_wrong_right','NFM_wrong_order','NFM_wrong_calls','NFM_wrong_sums','NFM_wrong_frame',f'NFM_wrong_window_{cut}']):
  jobs.append((42+8*cut+offset,h,'NFM_fixture --cfg '+flag))
jobs += [(97,'fast_dots::NFM_dots::terminal_selected_add',None),(98,'fast_dots::NFM_dots::terminal_selected_add','NFM_wrong_terminal_add'),(99,'fast_dots::NFM_dots::original_opening_descriptor',None),(100,'fast_dots::NFM_dots::original_opening_descriptor','NFM_wrong_descriptor')]
for i,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':'NFM_STRICT_PAYLOAD.json'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 negative=wrong or h.endswith('_wrong');expected='VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
