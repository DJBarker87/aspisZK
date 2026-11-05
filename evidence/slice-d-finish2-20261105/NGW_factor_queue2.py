from pathlib import Path
import subprocess,shutil
E=Path(__file__).resolve().parent
jobs=[('NGW_E003','extract','NGW_DotRef'),('NGW_L042','lean','NGW_ForwardRange'),('NGW_L049','lean','NGW_FactorIndex'),('NGW_L043','lean','NGW_FactorWrite'),('NGW_L044','lean','NGW_FactorCell'),('NGW_L050','lean','NGW_FactorLoops'),('NGW_L051','lean','NGW_FactorOuter'),('NGW_L052','lean','NGW_CircleCell'),('NGW_L053','lean','NGW_CircleLoop'),('NGW_L054','lean','NGW_CircleInitial'),('NGW_L055','lean','NGW_CircleOuter'),('NGW_L056','lean','NGW_NewModel'),('NGW_L045','lean','NGW_FactorRef/Types'),('NGW_L046','lean','NGW_FactorRef/Funs'),('NGW_L048','lean','NGW_FactorFrame')]
for a,k,n in jobs:
 if (E/a/'receipt.json').exists():continue
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,k,n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
 if k=='extract':
  dest=E/n;dest.mkdir(exist_ok=True)
  for p in(E/'NGW_extracted'/n/n).glob('*.lean'):shutil.copy2(p,dest/p.name)
