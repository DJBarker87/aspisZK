from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(28,'NHX_FactoredSuffix'),(29,'NHX_ProcessKind'),(30,'NHX_Powers7Edge'),(31,'NHX_ArraySlots')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
