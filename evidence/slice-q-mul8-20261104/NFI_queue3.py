from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(36,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(37,'NFI_copy::KMX_checks::KMX_ptr_wrong',None),(38,'NFI_original::original_proof_one_cell',None),(39,'NFI_original::original_proof_one_cell','NFI_wrong_original_cell')]
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_ORIGINAL_PAYLOAD.json','NFI_KANI_BASE':'NFI_ORIGINAL_BASE.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
