from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,target in [('NGC_L023','NGC_DigestRef/Types'),('NGC_L024','NGC_DigestRef/Funs'),('NGC_L025','NGC_DigestBridge'),('NGC_L026','NGC_KNE_Caller'),('NGC_L027','NGC_PreparationBoundary'),('NGC_L028','NGC_QueryPoststate'),('NGC_L029','NGC_WriterDomain')]:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
