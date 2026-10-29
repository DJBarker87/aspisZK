from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(77,'NDI_verifier','window_metadata_contract',''),(78,'NDI_verifier','window_metadata_contract','NDI_invert_metadata')]
for n,i in [(4,79),(16,81),(32,83)]:jobs.extend([(i,'NDI_verifier',f'raw{n}_isolated_window_contract',''),(i+1,'NDI_verifier',f'raw{n}_isolated_window_contract','NDI_invert_actual_raw')])
for target,cfg,i in [('tail_predicate_contract','NDI_invert_tail',85),('contains_predicate_contract','NDI_invert_contains',87),('iter_metadata_contract','NDI_invert_iter',89)]:jobs.extend([(i,'candidate::NDI_candidate',target,''),(i+1,'candidate::NDI_candidate',target,cfg)])
for i,m,target,cfg in jobs:
 env=dict(os.environ);env['NDI_RUST_CFG']=cfg
 subprocess.run(['python3',str(E/'NDI_run.py'),f'NDI_K{i:03}','kani','verifier::'+m+'::'+target],env=env,check=True)
subprocess.run(['python3',str(E/'NDI_run.py'),'NDI_E006','extract','predicates'],check=True)
