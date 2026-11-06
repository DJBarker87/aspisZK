from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,m in [(14,'NJJ_Value'),(15,'NJJ_Projection'),(16,'NJJ_Common')]:
 r=subprocess.run(['python3',str(E/'NJJ_run.py'),f'NJJ_L{n:03d}','lean',m]);assert r.returncode==0,(n,m)
