from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('dots_cursor_layout',None),('dots_cursor_layout','NFA_wrong_cursor_layout'),('dots_cursor_arbitrary_prestate',None),('dots_cursor_arbitrary_prestate','NFA_wrong_cursor_prestate'),('NFA_copy::KMX_checks::KMX_ptr_correct',None),('NFA_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,(name,wrong) in enumerate(jobs,12):
 a='NFA_K'+str(i).zfill(3);env={**os.environ,'NFA_KANI_PAYLOAD':'NFA_CURSOR_PAYLOAD.json'}
 if wrong:env['NFA_RUST_CFG']=wrong
 harness=name if name.startswith('NFA_copy') else 'fast_pairing::canonical::NFA_dot_ctor::'+name
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'kani',harness],env=env,stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 expected=1 if wrong or name.endswith('_wrong') else 0
 print(a,name,'exit',r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:break
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():break
