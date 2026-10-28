from pathlib import Path
import subprocess,json
E=Path(__file__).resolve().parent
jobs=[(31,'NDE_LinkBridge'),(32,'NDE_ClaimBridge'),(33,'NDE_ClaimResult'),(34,'NDE_ArrayExt'),(35,'NDE_PublicExt'),(36,'NDE_CarryInduction'),(37,'NDE_EmptyBridge')]
for n,t in jobs:
 if t=='NDE_ClaimResult' and json.loads((E/'NDE_L032/receipt.json').read_text())['exit_status']:continue
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)
