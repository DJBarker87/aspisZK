from pathlib import Path
import subprocess,shutil
E=Path(__file__).resolve().parent
jobs=[('NGW_E002','extract','NGW_FactorRef'),('NGW_L039','lean','NGW_FactorRow'),('NGW_L040','lean','NGW_ArrayLens'),('NGW_L041','lean','NGW_FactorIndex'),('NGW_L042','lean','NGW_ForwardRange'),('NGW_L043','lean','NGW_FactorWrite'),('NGW_L044','lean','NGW_FactorCell')]
for a,k,n in jobs:
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,k,n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if k=='extract':
  dest=E/n;dest.mkdir(exist_ok=True)
  for p in(E/'NGW_extracted'/n/n).glob('*.lean'):shutil.copy2(p,dest/p.name)
