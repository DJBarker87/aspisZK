from pathlib import Path
import os,subprocess,sys,json
E=Path(__file__).resolve().parent
jobs=[(14,'NFI_copy::KMX_checks::KMX_ptr_correct',None),(15,'NFI_copy::KMX_checks::KMX_ptr_wrong',None)]
windows=[('tail_initializer_frame','NFI_wrong_tail_init'),('raw_to_half0_frame','NFI_wrong_raw_half0'),('raw_to_half1_frame','NFI_wrong_raw_half1'),('private_cursor_to_step_frame','NFI_wrong_private_cursor'),('private_exhaust_to_caller_frame','NFI_wrong_private_exhaust'),('halves_to_count_frame','NFI_wrong_count_frame'),('finish_to_final_carrier_frame','NFI_wrong_final_carrier')]+[(f'tail_parser_push{i}_frame',f'NFI_wrong_tail_call{i}') for i in range(3)]
for i,(h,c) in enumerate(windows):
 for j,w in enumerate([None,c]):jobs.append((16+2*i+j,'fast_pairing::canonical::NFI_pairing::'+h,w))
for i,h,wrong in jobs:
 a=f'NFI_K{i:03}';env={**os.environ,'NFI_KANI_PAYLOAD':'NFI_TAIL_CALL_PAYLOAD.json'}
 if wrong:env['NFI_RUST_CFG']=wrong
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFI_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if wrong or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 log=(E/a/'stdout.log').read_text()
 if expected and 'VERIFICATION:- FAILED' not in log:sys.exit(2)
