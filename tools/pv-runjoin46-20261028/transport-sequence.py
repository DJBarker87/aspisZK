import subprocess,sys
from pathlib import Path
T=Path(__file__).parent
for a,label in enumerate(['Carrier','Map','Scalar','Complex','Quartic','Product','Installed'],61422):
 subprocess.run([sys.executable,str(T/'focused.py'),str(a),'R1Z.PV_RunJoin_Weight'+label+'46'],check=True)
