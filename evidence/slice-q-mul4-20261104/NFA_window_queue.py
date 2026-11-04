from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('fast_pairing::canonical::NFA_dot_ctor::dots_tail_source_window',None),('fast_pairing::canonical::NFA_dot_ctor::dots_tail_source_window','NFA_wrong_tail_source_window'),('NFA_copy::KMX_checks::KMX_ptr_correct',None),('NFA_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,(h,wrong) in enumerate(jobs,19):
 a='NFA_K'+str(i).zfill(3);env={**os.environ,'NFA_KANI_PAYLOAD':'NFA_WINDOW_PAYLOAD.json'}
 if wrong:env['NFA_RUST_CFG']=wrong
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'kani',h],env=env,stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,'exit',r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:break
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():break
