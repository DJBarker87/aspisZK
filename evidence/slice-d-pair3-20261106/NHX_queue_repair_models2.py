from pathlib import Path
import subprocess
E=Path(__file__).resolve().parent
for n,target in [(47,'NHX_FactoredPacket'),(48,'NHX_HighPost'),(49,'NHX_FinalLoop'),(50,'NHX_ProcessPorts')]:
 subprocess.run(['python3',str(E/'NHX_run.py'),f'NHX_L{n:03}','lean',target])
