from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[]
for name in ['tail_chain_window','tail_finish_context','tail_add_context','tail_argument_window','tail_readonly_window']:
 jobs.extend([(f'fast_pairing::canonical::NFC_dot_ctor::{name}',None), (f'fast_pairing::canonical::NFC_dot_ctor::{name}','NFC_wrong_'+name.removeprefix('tail_'))])
jobs += [('NFC_copy::KMX_checks::KMX_ptr_correct',None),('NFC_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,(h,wrong) in enumerate(jobs,5):
 a=f'NFC_K{i:03}';env={**os.environ}
 if wrong:env['NFC_RUST_CFG']=wrong
 r=subprocess.run(['python3',str(E/'NFC_kani_run.py'),a,'kani',h],env=env,stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:break
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():break
