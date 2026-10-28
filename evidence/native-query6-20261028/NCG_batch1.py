from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
for n,h in [(3,'single_negative'),(4,'eight'),(5,'eight_negative')]:
 r=subprocess.run([sys.executable,str(E/'NCG_run.py'),f'NCG_K{n:03}',f'NCG_{h}'])
 if r.returncode:raise SystemExit(r.returncode)
