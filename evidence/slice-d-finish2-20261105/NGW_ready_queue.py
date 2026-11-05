from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,n in [('NGW_L045','NGW_FactorRef/Types'),('NGW_L046','NGW_FactorRef/Funs'),('NGW_L047','NGW_FactorReference'),('NGW_L048','NGW_FactorFrame'),('NGW_L064','NGW_BoxModel'),('NGW_L066','NGW_FieldPorts')]:
 if (E/a/'receipt.json').exists():continue
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
