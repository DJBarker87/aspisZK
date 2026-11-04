from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('verifier::candidate::NFC_query_window::opening_prefix_window','NFC_wrong_opening_prefix'),('NFC_copy::KMX_checks::KMX_ptr_correct',None),('NFC_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,(h,wrong) in enumerate(jobs,23):
 a=f'NFC_K{i:03}';env={**os.environ,'NFC_KANI_PAYLOAD':'NFC_QUERY_PAYLOAD.json'}
 if wrong:env['NFC_RUST_CFG']=wrong
 r=subprocess.run(['python3',str(E/'NFC_kani_run.py'),a,'kani',h],env=env,stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:break
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():break
