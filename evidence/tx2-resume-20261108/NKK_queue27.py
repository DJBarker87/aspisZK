from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(77,'NKK_HeaderSource'),(78,'NKK_HeaderFactor')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
