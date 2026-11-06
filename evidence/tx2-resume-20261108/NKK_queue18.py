from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(62,'NKK_RawPrefix'),(48,'NKK_QueryStage'),(61,'NKK_AllocationStage')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
