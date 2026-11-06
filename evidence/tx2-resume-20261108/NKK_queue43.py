from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(106,'NKK_QueryEndJoin'),(107,'NKK_QueryDomain'),(108,'NKK_QueryWindows')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
