from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for number,module in enumerate(['NHM_FactoredTerm','NHM_GroupEncoding','NHM_DotResult','NHM_SharedPartials'],64):
 r=subprocess.run(['python3',str(E/'NHM_run.py'),f'NHM_L{number:03}','lean',module])
 if r.returncode:raise SystemExit(r.returncode)
