from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(16,'fast_dots::NFF_dots::main_term_window','NFF_wrong_main_term','NFF_ORDERED_PAYLOAD.json'),(17,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_ORDERED_PAYLOAD.json'),(18,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_ORDERED_PAYLOAD.json'),(19,'fast_pairing::canonical::NFF_pairing::raw_operand_window',None,'NFF_PAIRING_PAYLOAD.json'),(20,'fast_pairing::canonical::NFF_pairing::raw_operand_window','NFF_wrong_raw_operand','NFF_PAIRING_PAYLOAD.json'),(21,'fast_pairing::canonical::NFF_pairing::private_push_step_window',None,'NFF_PAIRING_PAYLOAD.json'),(22,'fast_pairing::canonical::NFF_pairing::private_push_step_window','NFF_wrong_private_step','NFF_PAIRING_PAYLOAD.json'),(23,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_PAIRING_PAYLOAD.json'),(24,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_PAIRING_PAYLOAD.json')]
for i,h,wrong,payload in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':payload}
 if payload=='NFF_PAIRING_PAYLOAD.json':env['NFF_KANI_BASE']='NFF_PAIRING_BASE.json'
 if wrong:env['NFF_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
