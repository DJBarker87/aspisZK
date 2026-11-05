from pathlib import Path
import subprocess,os,time
E=Path(__file__).resolve().parent
while not (E/'NGW_L060/receipt.json').exists():time.sleep(2)
for i in range(5):
 for inv in [False,True]:
  a=f'NGW_K{79+2*i+int(inv):03d}';env=dict(os.environ)
  if inv:env['NGW_INVERT']='1'
  with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'kani',f'weights::NGW_new::box_g{i}'],env=env,stdout=f,stderr=subprocess.STDOUT)
  print(a,r.returncode,flush=True)
  if r.returncode!=(1 if inv else 0):raise SystemExit('isolate unexpected result')
