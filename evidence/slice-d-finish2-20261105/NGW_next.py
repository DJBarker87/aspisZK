from pathlib import Path
import subprocess,time
E=Path(__file__).resolve().parent
# Serial continuation: no second host scope while the existing points queue runs.
while not (E/'NGW_K016/receipt.json').exists():time.sleep(2)
for a,n in [('NGW_L011','NGW_ConstructorArrays'),('NGW_L007','NGW_Reverse'),('NGW_L008','NGW_ConstructorSuccessorCell'),('NGW_L009','NGW_ConstructorSuccessor'),('NGW_L010','NGW_ConstructorPoints'),('NGW_L012','NGW_StepModel'),('NGW_L013','NGW_ProductLaw'),('NGW_L014','NGW_ReverseInduction')]:
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
