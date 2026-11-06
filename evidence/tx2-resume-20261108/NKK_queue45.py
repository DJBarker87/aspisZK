from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,k,t in [(118,'audit','batch10'),(114,'audit','scan'),(115,'sourcecheck','all'),(116,'export','all'),(117,'verify','all')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}',k,t])
 if r.returncode:break
