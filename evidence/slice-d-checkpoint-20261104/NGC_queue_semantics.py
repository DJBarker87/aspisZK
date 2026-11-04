from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
jobs=[('NGC_L043','lean','NGC_ValueBridge'),('NGC_L044','lean','NGC_AppendFrame'),('NGC_L045','lean','NGC_CheckpointBridge'),('NGC_E002','extract','NGC_HeapRef'),('NGC_E003','extract','NGC_FinishRef')]
for a,kind,target in jobs:
 with(E/(a+'-local.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGC_run.py'),a,kind,target],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
