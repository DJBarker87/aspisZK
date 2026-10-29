from pathlib import Path
import subprocess,os
E=Path(__file__).resolve().parent
for n in range(1,21):
 r=subprocess.run(['python3',str(E/'NDN_run.py'),f'NDN_E{n:03}','extract','NDN_scalar_windows'],env=dict(os.environ,NDN_EXTRACT_PARSER=str(n)))
 if r.returncode:raise SystemExit(r.returncode)
