from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for number,module in enumerate(['NHM_WindowExtracted','NHM_WindowBridge','NHM_ResultInvariant','NHM_ArrayPreserve','NHM_GroupCoefficient','NHM_GroupWeight','NHM_GroupWeightDomain','NHM_GroupCoefficientDomain'],24):
 r=subprocess.run(['python3',str(E/'NHM_run.py'),f'NHM_L{number:03}','lean',module])
 if r.returncode:raise SystemExit(r.returncode)
