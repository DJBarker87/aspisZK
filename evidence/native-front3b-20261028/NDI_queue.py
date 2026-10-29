from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[(68,"key_contract","NDI_invert_key_step"),(69,"key_initial_contract",""),(70,"key_initial_contract","NDI_invert_key_init"),(71,"range_contract",""),(72,"range_contract","NDI_invert_range"),(73,"keys_weak_contract",""),(74,"keys_real",""),(75,"keys_unimplied",""),(76,"keys_frame","")]
for i,target,cfg in jobs:
 env=dict(os.environ);env['NDI_RUST_CFG']=cfg
 subprocess.run(['python3',str(E/'NDI_run.py'),f'NDI_K{i:03}', 'kani','verifier::candidate::NDI_candidate::'+target],env=env,check=True)
