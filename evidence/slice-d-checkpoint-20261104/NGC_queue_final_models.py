from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,target in [('NGC_L054','NGC_FillInduction'),('NGC_L055','NGC_ReferenceValues'),('NGC_L056','NGC_FinishContents'),('NGC_L057','NGC_InitialInvariant')]:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
