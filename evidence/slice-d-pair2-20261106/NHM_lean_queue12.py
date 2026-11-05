from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for number,module in enumerate(['NHM_GroupDomains','NHM_EEncoding','NHM_ProofDriver'],51):
 r=subprocess.run(['python3',str(E/'NHM_run.py'),f'NHM_L{number:03}','lean',module])
 if r.returncode:raise SystemExit(r.returncode)
