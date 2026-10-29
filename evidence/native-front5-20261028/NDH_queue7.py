from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(74,'state_only_hiding::NDH_native::cmr_contract',None,'aspis-core'),(75,'state_only_hiding::NDH_native::cmr_contract','cmr','aspis-core'),(76,'pool_v1::format::NDH_native::policy_contract',None,'aspis-statement'),(77,'pool_v1::format::NDH_native::policy_contract','policy','aspis-statement'),(78,'pool_v1::format::NDH_native::short_decoders',None,'aspis-statement'),(79,'pool_v1::format::NDH_native::short_decoders','short','aspis-statement'),(80,'pool_v1::pair_tree_profile::NDH_native::afterstate_short',None,'aspis-statement')]
for i,target,invert,root in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 if root:env['NDH_ROOT']=root
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
