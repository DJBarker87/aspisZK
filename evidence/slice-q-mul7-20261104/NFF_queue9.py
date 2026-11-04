from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
names=[('head_return_window','NFF_wrong_head'),('initialized_arrays','NFF_wrong_init'),('inner_stop_endpoint','NFF_wrong_stop'),('main_decode_rejection','NFF_wrong_decode'),('prefix_reference_frame','NFF_wrong_prefix')]
jobs=[]
for i,(name,cfg) in enumerate(names):
 jobs.extend([(46+2*i,'fast_dots::NFF_dots::'+name,None),(47+2*i,'fast_dots::NFF_dots::'+name,cfg)])
jobs += [(56,'NFF_copy::KMX_checks::KMX_ptr_correct',None),(57,'NFF_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,h,cfg in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':'NFF_TERMINAL_PAYLOAD.json'}
 if cfg:env['NFF_RUST_CFG']=cfg
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if cfg or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():sys.exit(2)
