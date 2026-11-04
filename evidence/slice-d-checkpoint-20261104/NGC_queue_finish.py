from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('NGC_L022','lean','NGC_FinishFrame',False),('NGC_E001','extract','NGC_DigestRef',False)]
for a,kind,target,invert in jobs:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise RuntimeError(a)
r=subprocess.run(['python3',str(E/'NGC_finish_prepare.py')]);assert r.returncode==0
for k,name,invert in [(12,'finish_step',False),(13,'finish_step',True),(14,'finish_canonical',False),(15,'finish_canonical',True),(16,'finish_order',False),(17,'finish_order',True),(18,'raw_copy_positive',False),(19,'raw_copy_negative',False)]:
 a=f'NGC_K{k:03}';env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani','verifier::NGC_windows::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode!=(1 if invert or name.endswith('negative')else 0):break
