from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
jobs=[(52,'NLR_Inspect'),(53,'NLR_PrepareAll'),(54,'NLR_PrepareExact'),(55,'NLR_PrepareFinalSource'),(56,'NLR_PrepareFold'),(57,'NLR_PrepareSemantic137'),(58,'NLR_PrepareReachedDomain'),(59,'NLR_PrepareStep137'),(60,'NLR_PrepareSplitExtent')]
for n,m in jobs:
 a=f'NLR_L{n:03d}'
 assert not (P/a/'receipt.json').exists(),'Never resubmit'
 subprocess.run([sys.executable,str(P/'NLR_config.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a])
 if r.returncode: print(json.dumps(dict(stopped=a,module=m)),flush=True);sys.exit(r.returncode)
