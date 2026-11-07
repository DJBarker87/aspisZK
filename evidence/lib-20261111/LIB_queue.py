"""Serial convenience client; every module retains its own admitted scope."""
from pathlib import Path
import subprocess,sys
E=Path(__file__).resolve().parent
start=int(sys.argv[1])
for i,module in enumerate(sys.argv[2:],start):
 r=subprocess.run([sys.executable,str(E/'LIB_run.py'),f'LIB_L{i:03}','lean',module])
 if r.returncode:sys.exit(r.returncode)
