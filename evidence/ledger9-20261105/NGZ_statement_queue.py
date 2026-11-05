from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
for i,target in enumerate(['NGZ_PLAN_STATEMENTS','NGZ_WRITER_STATEMENTS','NGZ_POOL_STATEMENTS','NGZ_TX2_STATEMENTS','NGZ_ROOT_S','NGZ_ROOT_Q'],35):
 a='NGZ_L'+str(i).zfill(3)
 with (E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NGZ_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,target,r.returncode,flush=True)
 if r.returncode:print((E/(a+'-client.log')).read_text()[-4000:]);sys.exit(r.returncode)
