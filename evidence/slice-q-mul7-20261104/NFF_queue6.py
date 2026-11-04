from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(31,'fast_pairing::canonical::NFF_pairing::tail_chain_window',None,'NFF_TAIL_SPLIT_PAYLOAD.json'),(32,'fast_pairing::canonical::NFF_pairing::tail_chain_window','NFF_wrong_tail_chain','NFF_TAIL_SPLIT_PAYLOAD.json'),(33,'fast_pairing::canonical::NFF_pairing::tail_selected_finish_add',None,'NFF_TAIL_SPLIT_PAYLOAD.json'),(34,'fast_pairing::canonical::NFF_pairing::tail_selected_finish_add','NFF_wrong_tail_finish_add','NFF_TAIL_SPLIT_PAYLOAD.json'),(35,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_TAIL_SPLIT_PAYLOAD.json'),(36,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_TAIL_SPLIT_PAYLOAD.json')]
for i,h,wrong,payload in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':payload}
 if payload=='NFF_TAIL_SPLIT_PAYLOAD.json':env['NFF_KANI_BASE']='NFF_PAIRING_BASE.json'
 if wrong:env['NFF_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
