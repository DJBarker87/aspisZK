from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
jobs=[
('dots_outer_cursor',None),('dots_outer_cursor','NFA_wrong_dots_cursor'),
('dots_cursor_remaining',None),('dots_cursor_remaining','NFA_wrong_cursor_remaining'),
('dots_selected_g_frame',None),('dots_selected_g_frame','NFA_wrong_selected_g'),
('dots_wrapper_window',None),('dots_wrapper_window','NFA_wrong_wrapper_window'),
('NFA_copy::KMX_ptr_correct',None),('NFA_copy::KMX_ptr_wrong',None)]
for i,(name,wrong) in enumerate(jobs,1):
 a='NFA_K'+str(i).zfill(3);env={**os.environ}
 if wrong:env['NFA_RUST_CFG']=wrong
 harness=name if name.startswith('NFA_copy') else 'fast_pairing::canonical::NFA_dot_ctor::'+name
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'kani',harness],env=env,stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 expected=1 if wrong or name.endswith('_wrong') else 0
 print(a,harness,'exit',r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:break
 if expected:
  log=(E/a/'stdout.log').read_text()
  if 'VERIFICATION:- FAILED' not in log:print('Unexpected negative result; stop',flush=True);break
