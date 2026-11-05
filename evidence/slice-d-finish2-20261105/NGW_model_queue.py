from pathlib import Path
import subprocess,time,json
E=Path(__file__).resolve().parent
# Private scheduler yields before ABI setup; no scope overlap.
while not (E/'NGW_K098/receipt.json').exists():
 if 'isolate' in (E/'NGW_FINISH_NATIVE_QUEUE.log').read_text():break
 time.sleep(2)
jobs=[('NGW_L063','NGW_FactorLoops'),('NGW_L051','NGW_FactorOuter'),('NGW_L052','NGW_CircleCell'),('NGW_L053','NGW_CircleLoop'),('NGW_L054','NGW_CircleInitial'),('NGW_L055','NGW_CircleOuter'),('NGW_L056','NGW_NewModel'),('NGW_L045','NGW_FactorRef/Types'),('NGW_L046','NGW_FactorRef/Funs'),('NGW_L047','NGW_FactorReference'),('NGW_L048','NGW_FactorFrame'),('NGW_L064','NGW_BoxModel'),('NGW_L065','NGW_NewInterface')]
for a,n in jobs:
 if (E/a/'receipt.json').exists():continue
 with (E/(a+'-queue.log')).open('w')as f:r=subprocess.run(['python3',str(E/'NGW_run.py'),a,'lean',n],stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit(r.returncode)
