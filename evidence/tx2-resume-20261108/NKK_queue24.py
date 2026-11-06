from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for a,t in [(73,'NKK_SectionFrames'),(72,'NKK_FieldLiteral')]:
 r=subprocess.run(['python3',str(E/'NKK_run.py'),f'NKK_L{a:03}','lean',t])
 if r.returncode:break
