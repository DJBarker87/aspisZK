from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[('NGJ_L006','link','NGJ_ProofDriver'),('NGJ_L007','link','NGJ_Driver'),('NGJ_L008','audit','fixtures'),('NGJ_L009','audit','scan')]+[(f'NGJ_L{i+10:03}','audit',f'batch{i}') for i in range(16)]
for a,k,t in jobs:
 if (E/a/'receipt.json').exists():continue
 with (E/(a+'.client.log')).open('w') as f:r=subprocess.run(['python3',str(E/'NGJ_run.py'),a,k,t],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:break
