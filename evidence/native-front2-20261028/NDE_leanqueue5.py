from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(41,'NDE_LinkBridge'),(42,'NDE_ClaimResult'),(43,'NDE_PublicWindows')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)
