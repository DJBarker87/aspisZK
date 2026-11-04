from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for k,name,invert in [(4,'new_schedule',False),(5,'new_schedule',True),(6,'vector_copy_positive',False),(7,'vector_copy_negative',False)]:
 env=dict(os.environ)
 if invert:env['NGC_INVERT']='1'
 with (E/f'NGC_K{k:03}-local.log').open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),f'NGC_K{k:03}','kani','verifier::NGC_windows::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(k,r.returncode,flush=True)
 if r.returncode!=(1 if invert or name.endswith('negative')else 0):raise RuntimeError(k)
