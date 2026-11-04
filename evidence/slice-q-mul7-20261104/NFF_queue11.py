from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(68,'fast_pairing::canonical::NFF_pairing::raw_to_private_step',None),(69,'fast_pairing::canonical::NFF_pairing::raw_to_private_step','NFF_wrong_raw_step'),(70,'fast_pairing::canonical::NFF_pairing::private_finish_to_public_return',None),(71,'fast_pairing::canonical::NFF_pairing::private_finish_to_public_return','NFF_wrong_finish_return'),(72,'NFF_copy::KMX_checks::KMX_ptr_correct',None),(73,'NFF_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,h,cfg in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':'NFF_RAW_STEP_PAYLOAD.json','NFF_KANI_BASE':'NFF_PAIRING_BASE.json'}
 if cfg:env['NFF_RUST_CFG']=cfg
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if cfg or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():sys.exit(2)
