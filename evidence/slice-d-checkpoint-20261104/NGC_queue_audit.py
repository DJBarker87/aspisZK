from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,kind,target in [('NGC_L015','linkaudit','NGC_Driver'),('NGC_L016','auditbin','fixtures'),('NGC_L017','auditbin','proof0'),('NGC_L018','auditbin','scan'),('NGC_L019','lean','NGC_FinishFrame'),('NGC_E001','extract','NGC_DigestRef')]:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
