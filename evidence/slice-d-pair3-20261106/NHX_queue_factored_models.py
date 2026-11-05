from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(19,'NHX_FactoredCut'),(20,'NHX_FactoredSuffix')]:
 r=subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target]);
 if r.returncode:break
