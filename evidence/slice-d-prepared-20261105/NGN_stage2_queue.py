from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
jobs=[('NGN_K013','kani','verifier::NGN_stages::powers_assignment',True),('NGN_L006','lean','NGN_FrameChain',False),('NGN_L007','lean','NGN_Emitted',False)]
for a,k,t,inv in jobs:
 env=dict(os.environ)
 if inv:env['NGN_INVERT']='1'
 r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,k,t],env=env,capture_output=True,text=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr);print(a,r.returncode,r.stdout[-300:],flush=True)
 if (r.returncode==0)==inv:raise RuntimeError('unexpected result')
