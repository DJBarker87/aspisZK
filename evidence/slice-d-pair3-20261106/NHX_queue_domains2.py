from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(52,'NHX_FactoredPacket'),(53,'NHX_KindIndex'),(54,'NHX_KWordLift')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
