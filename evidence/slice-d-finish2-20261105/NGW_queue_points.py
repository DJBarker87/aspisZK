from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
cases=['copy_control_gate','step_g0','step_g1','step_g2','step_g3','step_g4','absorption','control_gate']
for i,name in enumerate(cases):
 for inv in [False,True]:
  a=f'NGW_K{2*i+1+int(inv):03d}';
  if (E/a/'receipt.json').exists():continue
  env=dict(os.environ,NGW_CORE='1')
  if inv:env['NGW_INVERT']='1'
  with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'kani','state_only_prefix::NGW_points::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
  print(a,r.returncode,flush=True)
  if not (E/a/'receipt.json').exists():raise SystemExit('no receipt')
  if r.returncode != (1 if inv else 0):raise SystemExit('isolate unexpected outcome')
