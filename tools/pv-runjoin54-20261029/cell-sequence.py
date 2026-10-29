import subprocess,sys
from pathlib import Path
T=Path(__file__).parent
for a,m in [(66906,'R24Cell1_54'),(66907,'R24Cell2_54'),(66908,'R24Cell3_54'),(66909,'R24Decompose54')]:
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(a),'R1Z.PV_RunJoin_'+m])
 if r.returncode:sys.exit(r.returncode)
