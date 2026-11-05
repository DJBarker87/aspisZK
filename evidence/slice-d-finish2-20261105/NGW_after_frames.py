from pathlib import Path
import subprocess,time
E=Path(__file__).resolve().parent
while not (E/'NGW_K030/receipt.json').exists():time.sleep(2)
for a,kind,n in [('NGW_E001','extract','NGW_HelperRef'),('NGW_L015','lean','NGW_StepModel'),('NGW_L013','lean','NGW_ProductLaw'),('NGW_L014','lean','NGW_ReverseInduction'),('NGW_L016','lean','NGW_PointsPacket'),('NGW_L017','lean','NGW_WordExt')]:
 with (E/(a+'-queue.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,kind,n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
