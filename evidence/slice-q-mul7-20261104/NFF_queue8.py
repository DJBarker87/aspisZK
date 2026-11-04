from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(45,'fast_dots::NFF_dots::tail_argument_window',None,'NFF_ARGUMENT_PAYLOAD.json'),(38,'fast_dots::NFF_dots::tail_argument_window','NFF_wrong_tail_arguments','NFF_ARGUMENT_PAYLOAD.json'),(41,'fast_dots::NFF_dots::native_inner_range_step',None,'NFF_ARGUMENT_PAYLOAD.json'),(42,'fast_dots::NFF_dots::native_inner_range_step','NFF_wrong_inner_range','NFF_ARGUMENT_PAYLOAD.json'),(43,'fast_dots::NFF_dots::native_outer_cursor_step',None,'NFF_ARGUMENT_PAYLOAD.json'),(44,'fast_dots::NFF_dots::native_outer_cursor_step','NFF_wrong_outer_cursor','NFF_ARGUMENT_PAYLOAD.json'),(39,'NFF_copy::KMX_checks::KMX_ptr_correct',None,'NFF_ARGUMENT_PAYLOAD.json'),(40,'NFF_copy::KMX_checks::KMX_ptr_wrong',None,'NFF_ARGUMENT_PAYLOAD.json')]
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
