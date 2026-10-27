"""Sequential focused task targets; unchanged admission/launcher per target."""
from pathlib import Path
import sys,subprocess
P=Path(__file__).resolve().parent;n=int(sys.argv[1])
for module in sys.argv[2:]:
 assert 1<=n<=100
 with (P/f'JGh_TX2_{n:03}-driver.log').open('w') as f:
  r=subprocess.run([sys.executable,str(P/'JGh_TX2_compile.py'),str(n),module],stdout=f,stderr=subprocess.STDOUT)
 print(n,module,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 n+=1
