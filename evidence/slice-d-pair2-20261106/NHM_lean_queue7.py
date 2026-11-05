from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for number,module in enumerate(['NHM_ControlLoop','NHM_GroupAccum','NHM_GroupAccumDomain','NHM_GroupRoot'],42):
 r=subprocess.run(['python3',str(E/'NHM_run.py'),f'NHM_L{number:03}','lean',module])
 if r.returncode:raise SystemExit(r.returncode)
