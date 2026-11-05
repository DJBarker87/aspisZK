from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
cases=['write_frame','write_window','point_lookup']+[f'circle_g{i}'for i in [0,1,2,3,4,6,7]]+[f'initial_g{i}'for i in [0,1,3,4]]+['control']
for i,n in enumerate(cases):
 for inv in [False,True]:
  a=f'NGW_K{49+2*i+int(inv):03d}';env=dict(os.environ)
  if inv:env['NGW_INVERT']='1'
  with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'kani','weights::NGW_new::'+n],env=env,stdout=f,stderr=subprocess.STDOUT)
  print(a,r.returncode,flush=True)
  if r.returncode!=(1 if inv else 0):raise SystemExit('isolate unexpected result')
