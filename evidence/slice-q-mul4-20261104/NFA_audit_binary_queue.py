from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
modes=[56,57,45,46,47,48,49,50,51,52,53,54]
for i,mode in enumerate(modes,80):
 a='NFA_L'+str(i).zfill(3)
 r=subprocess.run(['python3',str(E/'NFA_run.py'),a,'auditbin',str(mode)],env={**os.environ,'NFA_SINT2_FIRST':'1'},stdout=(E/(a+'-client.log')).open('w'),stderr=subprocess.STDOUT)
 print(a,'mode',mode,'exit',r.returncode,flush=True)
 if r.returncode:break
