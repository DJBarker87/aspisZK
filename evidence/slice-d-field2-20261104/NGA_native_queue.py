from pathlib import Path
import subprocess,os,json,sys
E=Path(__file__).resolve().parent
jobs=[(2,'copy_negative',False,1),(3,'outer2',False,0),(4,'outer2',True,1),(5,'outer3',False,0),(6,'outer3',True,1),(7,'outer4',False,0),(8,'outer4',True,1)]
for number,name,invert,expected in jobs:
 a=f'NGA_K{number:03}';env=dict(os.environ,NGA_CORE='1')
 if invert:env['NGA_INVERT']='1'
 with (E/(a+'-client.log')).open('w') as f:
  r=subprocess.run([sys.executable,str(E/'NGA_run.py'),a,'kani','field::NGA_outer::'+name],env=env,stdout=f,stderr=subprocess.STDOUT)
 print(json.dumps(dict(attempt=a,harness=name,exit=r.returncode,expected=expected)),flush=True)
 if r.returncode!=expected:raise SystemExit('STOP unexpected verdict; inspect recorded attempt, do not retry unchanged')
