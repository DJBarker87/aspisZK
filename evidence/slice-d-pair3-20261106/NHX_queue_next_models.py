from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(32,'NHX_FactoredCut'),(33,'NHX_FactoredSuffix'),(34,'NHX_ProcessKind'),(35,'NHX_ArraySlots')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
