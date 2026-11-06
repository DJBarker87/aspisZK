from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(32,'NKK_RawChain'),(33,'NKK_RunEval'),(34,'NKK_RawAssociation'),(35,'NKK_CloseTail'),(36,'NKK_ClausesRun'),(37,'NKK_RawSlots'),(38,'NKK_RawSynchrony'),(39,'NKK_RawLength')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
