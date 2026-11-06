from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(102,'NKK_QueryBlockJoin'),(103,'NKK_QueryMidJoin'),(104,'NKK_QueryEndJoin')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
