from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
jobs=[(65+h,f'JGk_TX2_Lookup{h:02}') for h in range(1,5)]+[(70,'JGk_TX2_Obstruction70')]+[(66+h,f'JGk_TX2_Lookup{h:02}') for h in range(5,18)]
for n,mod in jobs:
 r=subprocess.run([sys.executable,str(P/'JGk_TX2_compile.py'),str(n),mod],stdout=(P/f'JGk_TX2_{n:03}-driver.log').open('w'),stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
