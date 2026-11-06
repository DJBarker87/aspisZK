from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(88,'NKK_DigestSource'),(87,'NKK_ResumeBodyFactor')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
