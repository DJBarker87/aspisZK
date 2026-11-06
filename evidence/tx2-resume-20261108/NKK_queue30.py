from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(83,'NKK_FieldStages'),(84,'NKK_DigestSource')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
