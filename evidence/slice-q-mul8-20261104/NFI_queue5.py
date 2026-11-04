from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(51,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(52,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,n in enumerate(['q_receiver','g_receiver','q_return']):
 for j,w in enumerate([None,'NFI_wrong_'+n+'_disjoint']):jobs.append((53+2*i+j,'fast_pairing::canonical::NFI_pairing::'+n+'_disjoint',w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_DISJOINT_PAYLOAD.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
