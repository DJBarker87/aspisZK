from pathlib import Path
import subprocess,sys,os,json
E=Path(__file__).resolve().parent
for i,name in enumerate(['gamma_stage','kappa_stage','alpha0_stage','rho_stage','query_stage']):
 for invert in [False,True]:
  a=f'NGN_K{16+2*i+int(invert):03d}';env=dict(os.environ)
  if invert:env['NGN_INVERT']='1'
  r=subprocess.run([sys.executable,str(E/'NGN_run.py'),a,'kani','verifier::NGN_stages::'+name],env=env,text=True,capture_output=True);(E/(a+'-client.log')).write_text(r.stdout+r.stderr)
  out=(E/a/'stdout.log').read_text() if (E/a/'stdout.log').exists() else ''
  good=('VERIFICATION:- FAILED' in out if invert else 'VERIFICATION:- SUCCESSFUL' in out)
  print(a,r.returncode,'expected',good,flush=True)
  if not good:print(r.stdout[-1200:],flush=True);sys.exit(1)
