from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[('NGC_L046','NGC_AppendFrame'),('NGC_L047','NGC_FinishContents'),('NGC_L048','NGC_NFW_QueryEntry'),('NGC_L049','NGC_HeapRef/Types'),('NGC_L050','NGC_HeapRef/Funs'),('NGC_L051','NGC_FinishRef/Types'),('NGC_L052','NGC_FinishRef/Funs'),('NGC_L053','NGC_RefInspect')]
for a,target in jobs:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,'lean',target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
