from pathlib import Path
import subprocess,json,sys
E=Path(__file__).resolve().parent
jobs=[('NGZ_L004','lean','NGZ_ProofDriver'),('NGZ_L005','link','NGZ_ProofDriver'),('NGZ_L006','lean','NGZ_Driver'),('NGZ_L007','link','NGZ_Driver')]+[('NGZ_L'+str(i+8).zfill(3),'audit','batch'+str(i))for i in range(24)]+[('NGZ_L032','audit','fixtures'),('NGZ_L033','audit','scan')]
for a,kind,target in jobs:
 if (E/a/'receipt.json').exists():
  assert json.loads((E/a/'receipt.json').read_text())['exit_status']==0;continue
 with (E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NGZ_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,kind,target,r.returncode,flush=True)
 if r.returncode:print((E/(a+'-client.log')).read_text()[-5000:],flush=True);sys.exit(r.returncode)
