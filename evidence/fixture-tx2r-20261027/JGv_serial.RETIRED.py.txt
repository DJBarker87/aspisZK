"""Serial task driver; stop on first failure, never overlap own scopes."""
from pathlib import Path
import subprocess,sys
p=Path(__file__).parent
n=int(sys.argv[1])
for mod in sys.argv[2:]:
 r=subprocess.run([sys.executable,str(p/'JGv_TX2_compile.py'),str(n),mod])
 if r.returncode:sys.exit(r.returncode)
 n+=1
