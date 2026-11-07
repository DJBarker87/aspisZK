from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
jobs=[(10,'NLR_PrepareTails'),(7,'NLR_PrepareTailSource'),(8,'NLR_ObserverSites'),(11,'NLR_WindowFrame'),(12,'NLR_PrepareDenote')]
phases=['allocate','split','semanticRange','expandSemantic','valueRange','expandValues','rebuild','view','semantic','mapSemantic','mark','constructor']
n=13
for kind in ['Frame','Progress','Run']:
 for phase in phases:
  jobs.append((n,'NLR_Prepare'+kind+'_'+phase));n+=1
for n,m in jobs:
 a=f'NLR_L{n:03d}'
 if (P/a/'receipt.json').exists():continue
 subprocess.run([sys.executable,str(P/'NLR_config.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a])
 if r.returncode: print(json.dumps(dict(stopped=a,module=m)),flush=True);sys.exit(r.returncode)
