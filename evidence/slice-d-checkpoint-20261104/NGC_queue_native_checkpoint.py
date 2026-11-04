from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for script in ['NGC_checkpoint_prepare.py','NGC_checkpoint_control_prepare.py']:
 r=subprocess.run(['python3',str(E/script)]);assert r.returncode==0
for k,name,invert in [(30,'checkpoint_transition',False),(31,'checkpoint_transition',True),(32,'checkpoint_copy_positive',False),(33,'checkpoint_copy_negative',False),(34,'checkpoint_order',False),(35,'checkpoint_order',True)]:
 a=f'NGC_K{k:03}';env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani','verifier::NGC_windows::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode!=(1 if invert or name.endswith('negative')else 0):break
