from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,k,n in [('NGW_L078','lean','NGW_COMBINED_IMPORT'),('NGW_L079','auditbin','proof0'),('NGW_L080','auditbin','scan')]:
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,k,n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
