from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
names=[('native_chunk_continuation','NFF_wrong_chunk'),('native_tail_parse_total','NFF_wrong_tail_total'),('native_main_parse_window','NFF_wrong_main_parse'),('native_wrapper_short_prefix','NFF_wrong_short')]
jobs=[]
for i,(name,cfg) in enumerate(names):
 jobs.extend([(58+2*i,'fast_dots::NFF_dots::'+name,None),(59+2*i,'fast_dots::NFF_dots::'+name,cfg)])
jobs += [(66,'NFF_copy::KMX_checks::KMX_ptr_correct',None),(67,'NFF_copy::KMX_checks::KMX_ptr_wrong',None)]
for i,h,cfg in jobs:
 a=f'NFF_K{i:03}';env={**os.environ,'NFF_KANI_PAYLOAD':'NFF_TOTAL_PARSE_PAYLOAD.json'}
 if cfg:env['NFF_RUST_CFG']=cfg
 with (E/(a+'-client.log')).open('w') as out:r=subprocess.run(['python3',str(E/'NFF_kani_run.py'),a,'kani',h],env=env,stdout=out,stderr=subprocess.STDOUT)
 expected=1 if cfg or h.endswith('_wrong') else 0
 print(a,r.returncode,'expected',expected,flush=True)
 if r.returncode!=expected:sys.exit(1)
 if expected and 'VERIFICATION:- FAILED' not in (E/a/'stdout.log').read_text():sys.exit(2)
