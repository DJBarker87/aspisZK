from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,kind,target in [('NGC_L020','auditbin','scan'),('NGC_L021','lean','NGC_FinishFrame'),('NGC_E001','extract','NGC_DigestRef')]:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
