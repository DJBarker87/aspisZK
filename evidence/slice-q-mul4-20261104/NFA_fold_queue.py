from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for i,name in enumerate(['NFA_ArrayShape','NFA_FoldLane','NFA_FoldEight','NFA_Iterator','NFA_OuterStep'],52):
 a='NFA_L'+str(i).zfill(3)
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'lean',name],env={**os.environ,'NFA_SINT2_FIRST':'1'},stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 print(a,name,'exit',r.returncode,flush=True)
 if r.returncode:break
