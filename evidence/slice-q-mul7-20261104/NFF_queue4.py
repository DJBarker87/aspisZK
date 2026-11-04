from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(25,'fast_pairing::canonical::NFF_pairing::public_push_context',None,'NFF_PUBLIC_PAYLOAD.json'),(26,'fast_pairing::canonical::NFF_pairing::public_push_context','NFF_wrong_public_push','NFF_PUBLIC_PAYLOAD.json'),(27,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_PUBLIC_PAYLOAD.json'),(28,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_PUBLIC_PAYLOAD.json')]
for i,h,wrong,payload in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':payload}
 if payload in ['NFF_PAIRING_PAYLOAD.json','NFF_PUBLIC_PAYLOAD.json']:env['NFF_KANI_BASE']='NFF_PAIRING_BASE.json'
 if wrong:env['NFF_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
