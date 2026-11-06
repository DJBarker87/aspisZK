from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(81,'NKK_HeaderFactor'),(82,'NKK_FieldCps'),(80,'NKK_FieldStages')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
