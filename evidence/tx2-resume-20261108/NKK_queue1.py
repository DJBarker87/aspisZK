from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
jobs=[('L009','lean','NKK_ClausesQueryEnd',{}),('L010','lean','NKK_ClausesQueryMid',{}),('L011','lean','NKK_ClausesQueryBlock',{}),('L012','lean','NKK_ClausesResumeBody',{}),('L013','lean','NKK_ClausesRun',{}),('L014','lean','NKK_NativeRaw',{})]
for a,k,t,env in jobs:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),'NKK_'+a,k,t],env={**os.environ,**env})
 if r.returncode:break
