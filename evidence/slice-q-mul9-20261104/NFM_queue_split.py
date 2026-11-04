from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
jobs=[(42,'NFM_copy::KMX_checks::KMX_ptr_correct',None),(43,'NFM_copy::KMX_checks::KMX_ptr_wrong',None)]
for cut in range(7):
 h=f'fast_dots::NFM_dots::window_{cut}';jobs.append((44+7*cut,h,None))
 for offset,flag in enumerate(['NFM_wrong_left','NFM_wrong_right','NFM_wrong_order','NFM_wrong_sums','NFM_wrong_frame','NFM_wrong_limbs']):
  jobs.append((45+7*cut+offset,h,'NFM_fixture --cfg '+flag))
jobs += [(93,'fast_dots::NFM_dots::terminal_selected_add',None),(94,'fast_dots::NFM_dots::terminal_selected_add','NFM_wrong_terminal_add'),(95,'fast_dots::NFM_dots::original_opening_descriptor',None),(96,'fast_dots::NFM_dots::original_opening_descriptor','NFM_wrong_descriptor'),(97,'fast_dots::NFM_dots::fold_borrowed_frame',None),(98,'fast_dots::NFM_dots::fold_borrowed_frame','NFM_wrong_fold_frame'),(99,'fast_dots::NFM_dots::head_borrowed_frame',None),(100,'fast_dots::NFM_dots::head_borrowed_frame','NFM_wrong_head_frame')]
for i,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':'NFM_SPLIT_FRAME_PAYLOAD.json'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 negative=wrong or h.endswith('_wrong');expected='VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
