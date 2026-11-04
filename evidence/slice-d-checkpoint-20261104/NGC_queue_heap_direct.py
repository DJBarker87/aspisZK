from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent;k=42
for method in ['direct_zero','direct_one','direct_overflow','resize_step','clone_value']:
 for typ in ['u8','q','raw','wide']:
  for invert in [False,True]:
   a=f'NGC_K{k:03}';name=method+'_'+typ;env=dict(os.environ)
   if invert:env['NGC_INVERT']='1'
   with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'kani','verifier::NGC_windows::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
   print(a,name,r.returncode,flush=True)
   if r.returncode!=(1 if invert else 0):raise RuntimeError(a)
   k+=1
