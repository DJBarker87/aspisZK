from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(28,'NKK_RawFold'),(29,'NKK_RawAssociation'),(30,'NKK_Invoke'),(31,'NKK_ClausesRun')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
