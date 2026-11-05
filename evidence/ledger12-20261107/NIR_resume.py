from pathlib import Path
import json,subprocess,sys
E=Path(__file__).resolve().parent
for i,group in enumerate(range(3,29),15):
 r=subprocess.run([sys.executable,str(E/'NIR_run.py'),f'NIR_L{i:03}','audit','batch'+str(group)])
 if r.returncode:
  print(f'NIR audit stopped L{i:03}; exit {r.returncode}',flush=True);sys.exit(r.returncode)
