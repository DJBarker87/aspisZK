from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(16,'NKK_ClausesQueryMid'),(17,'NKK_ClausesQueryBlock'),(18,'NKK_ClausesResumeBody'),(19,'NKK_ClausesRun'),(20,'NKK_NativeRaw'),(21,'NKK_RawChain')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
