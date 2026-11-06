from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,k in [(20,'export'),(21,'verify')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}',k,'all'])
 if r.returncode:break
