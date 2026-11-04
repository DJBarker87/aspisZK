from pathlib import Path
import os,subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[(5,'gamma_stage',True),(6,'kappa_stage',False),(7,'kappa_stage',True),(8,'alpha0_stage',False),(9,'alpha0_stage',True),(10,'rho_stage',False),(11,'rho_stage',True)]
for n,name,invert in jobs:
 a=f'NGN_K{n:03d}'; env=dict(os.environ)
 if invert:env['NGN_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,'kani','verifier::NGN_stages::'+name],env=env,capture_output=True,text=True)
 (E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 print(a,r.returncode,flush=True)
 if not (E/a/'receipt.json').exists():raise RuntimeError('prelaunch/transport failure: recover before continuing')
 x=json.loads((E/a/'receipt.json').read_text());out=(E/a/'stdout.log').read_text();good=('VERIFICATION:- FAILED' in out if invert else 'VERIFICATION:- SUCCESSFUL' in out)
 if not good:print(out[-3500:],flush=True);break
