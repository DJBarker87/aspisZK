from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,t in [(38,'NDE_LinkBridge'),(39,'NDE_ClaimResult'),(40,'NDE_MulStubValue')]:
 r=subprocess.run(['python3',str(E/'NDE_run.py'),f'NDE_L{n:03}','lean',t])
 if r.returncode:raise SystemExit(r.returncode)
