from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(47,'sampler::NDH_native::decode_contract',None,None),(48,'sampler::NDH_native::decode_contract','decode8',None),(49,'sampler::NDH_native::add_step_contract',None,None),(50,'sampler::NDH_native::add_step_contract','add_step',None),(51,'r0_transcript::NDH_native::finish_contract',None,'aspis-core'),(52,'r0_transcript::NDH_native::finish_contract','finish','aspis-core'),(53,'r0_transcript::NDH_native::rank_word',None,'aspis-core'),(54,'r0_transcript::NDH_native::rank_word_wrong',None,'aspis-core')]
for i,target,invert,root in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 if root:env['NDH_ROOT']=root
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
