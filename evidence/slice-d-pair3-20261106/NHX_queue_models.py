from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(8,'NHX_GroupPacket'),(9,'NHX_FactoredTail'),(10,'NHX_SharedPacket')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
