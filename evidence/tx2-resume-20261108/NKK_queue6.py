from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(31,'NKK_ClausesRun'),(32,'NKK_RawChain'),(33,'NKK_RunEval'),(34,'NKK_RawAssociation')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
