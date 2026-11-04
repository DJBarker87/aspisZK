from pathlib import Path
import subprocess,sys,os
E=Path(__file__).resolve().parent
for n,control in [(29,None),(30,'NGN_BAD_BOX_VALUE'),(31,'NGN_BAD_ALLOC')]:
 a=f'NGN_K{n:03d}';env=dict(os.environ)
 if control:env[control]='1'
 r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,'kani','verifier::NGN_stages::boxed_ownership'],env=env,text=True,capture_output=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
 out=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else '';good=('VERIFICATION:- FAILED' in out if control else 'VERIFICATION:- SUCCESSFUL' in out);print(a,r.returncode,'expected',good,flush=True)
 if not good:print(r.stdout[-1300:],flush=True);sys.exit(1)
