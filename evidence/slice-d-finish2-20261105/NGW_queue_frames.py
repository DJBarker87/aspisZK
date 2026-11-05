from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for i,name in enumerate(['wrapper_g0','wrapper_g1','wrapper_g2','wrapper_g3','return_frame','init_successor','init_absorption']):
 for inv in [False,True]:
  a=f'NGW_K{17+2*i+int(inv):03d}';env=dict(os.environ,NGW_CORE='1')
  if inv:env['NGW_INVERT']='1'
  with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'kani','state_only_prefix::NGW_points::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
  print(a,r.returncode,flush=True)
  if r.returncode!=(1 if inv else 0):raise SystemExit('unexpected outcome; isolate')
