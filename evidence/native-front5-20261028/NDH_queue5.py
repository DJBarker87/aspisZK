from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(55,'sampler::NDH_native::decode_contract',None,None),(56,'sampler::NDH_native::decode_contract','decode8',None),(57,'r0_transcript::NDH_native::finish_contract',None,'aspis-core'),(58,'r0_transcript::NDH_native::finish_contract','finish','aspis-core'),(59,'transcript::NDH_native::absorb_bytes',None,None),(60,'transcript::NDH_native::absorb_bytes','absorb',None),(61,'transcript::NDH_native::new_bytes',None,None),(62,'transcript::NDH_native::new_bytes','new_transcript',None)]
for i,target,invert,root in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 if root:env['NDH_ROOT']=root
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
