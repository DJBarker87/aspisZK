"""ONE serial full combined audit, after focused modules and unchanged fixtures."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n in range(39,48):
 a=f'NKB_L{n:03d}';r=subprocess.run([sys.executable,str(E/'NKB_run.py'),a])
 if r.returncode:
  print(a+' STOP; inspect the receipt before another launch',flush=True);raise SystemExit(r.returncode)
print('NKB combined audit sequence completed',flush=True)
