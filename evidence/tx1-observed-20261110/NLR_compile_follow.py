from pathlib import Path
import subprocess,sys,json
P=Path(__file__).resolve().parent
jobs=[(52,'NLR_Inspect'),(53,'NLR_PrepareAll'),(54,'NLR_PrepareExact'),(55,'NLR_PrepareFinalSource'),(56,'NLR_PrepareFold'),(57,'NLR_PrepareSemantic137'),(58,'NLR_PrepareReachedDomain'),(59,'NLR_PrepareStep137'),(60,'NLR_PrepareSplitExtent'),(61,'NLR_ObservedSuccess'),(62,'NLR_ObservedFinish'),(63,'NLR_FinishModelDomain'),(70,'NLR_ConvertedReply'),(71,'NLR_SemanticCallerResult')]
for n,m in jobs:
 a=f'NLR_L{n:03d}'
 if (P/a/'receipt.json').exists():
  current=(P/'NLR_generated'/(m+'.lean')).read_bytes()
  good=[]
  for f in P.glob('NLR_L[0-9][0-9][0-9]/receipt.json'):
   r=json.loads(f.read_text());src=f.parent/'sources/NLR_generated'/(m+'.lean')
   if r['exit_status']==0 and r.get('module')==m and src.is_file() and src.read_bytes()==current:good.append(f)
  assert good,(a,m,'Choose a fresh attempt for changed input; never resubmit')
  continue
 subprocess.run([sys.executable,str(P/'NLR_config.py'),a,m],check=True)
 r=subprocess.run([sys.executable,str(P/'NLR_run.py'),a])
 if r.returncode: print(json.dumps(dict(stopped=a,module=m)),flush=True);sys.exit(r.returncode)
