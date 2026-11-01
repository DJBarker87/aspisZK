from pathlib import Path
import subprocess,sys
T=Path(__file__).parent
for i,m in enumerate(sys.argv[2:],int(sys.argv[1])):
 r=subprocess.run([sys.executable,str(T/'focused.py'),str(i),'R1Z.'+m])
 if r.returncode:sys.exit(r.returncode)
