from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(63,'pool_v1::verifier_registry::NDH_native::binding_contract',None,'aspis-statement'),(64,'pool_v1::verifier_registry::NDH_native::binding_contract','binding','aspis-statement'),(65,'pool_v1::verifier_registry::NDH_native::status_all',None,'aspis-statement'),(66,'pool_v1::verifier_registry::NDH_native::status_wrong',None,'aspis-statement'),(67,'NDH_program::admission_contract',None,'program'),(68,'NDH_program::admission_contract','admission','program'),(69,'r0::heap::NDH_native::fill_empty',None,'aspis-core'),(70,'r0::heap::NDH_native::fill_one',None,'aspis-core'),(71,'r0::heap::NDH_native::fill_one','fill','aspis-core'),(72,'sampler::NDH_native::qwrite_contract',None,None),(73,'sampler::NDH_native::qwrite_contract','qwrite',None)]
for i,target,invert,root in jobs:
 env=dict(os.environ)
 if invert:env['NDH_INVERT']=invert
 if root:env['NDH_ROOT']=root
 a=f'NDH_K{i:03}'
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NDH_run.py'),a,'kani',target],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('wrapper failure; inspect before continuing')
