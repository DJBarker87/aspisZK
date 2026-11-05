from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in[(58,'NHX_ProcessPost'),(59,'NHX_RegularPost')]:
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
 if r.returncode:break
