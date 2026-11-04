from pathlib import Path
import subprocess,os,sys
E=Path(__file__).resolve().parent
jobs=[
(93,'NFM_SPLIT_FRAME_PAYLOAD.json','fast_dots::NFM_dots::terminal_selected_add',None),
(94,'NFM_SPLIT_FRAME_PAYLOAD.json','fast_dots::NFM_dots::terminal_selected_add','NFM_wrong_terminal_add'),
(95,'NFM_FINAL_FRAME_PAYLOAD.json','NFM_copy::KMX_checks::KMX_ptr_correct',None),
(96,'NFM_FINAL_FRAME_PAYLOAD.json','NFM_copy::KMX_checks::KMX_ptr_wrong',None),
(97,'NFM_CONTROL_PAYLOAD.json','NFM_copy::KMX_checks::KMX_ptr_correct',None),
(98,'NFM_CONTROL_PAYLOAD.json','NFM_copy::KMX_checks::KMX_ptr_wrong',None),
(99,'NFM_FINAL_FRAME_PAYLOAD.json','fast_dots::NFM_dots::final_fold_head_frame',None),
(100,'NFM_FINAL_FRAME_PAYLOAD.json','fast_dots::NFM_dots::final_fold_head_frame','NFM_wrong_final_frame')]
for i,payload,h,wrong in jobs:
 a=f'NFM_K{i:03}';env={**os.environ,'NFM_KANI_PAYLOAD':payload,'NFM_FINAL_QUEUE':'1'}
 if wrong:env['NFM_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFM_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 log=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
 negative=wrong or h.endswith('_wrong');expected='VERIFICATION:- FAILED' if negative else 'VERIFICATION:- SUCCESSFUL'
 good=expected in log and 'TIMEOUT' not in log and 'timed out' not in log
 print(a,h,r.returncode,good,flush=True)
 if not good:sys.exit(1)
