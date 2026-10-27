from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
n=5
for tree,heights in [(0,range(16,-1,-1)),(2,range(17,-1,-1))]:
 for h in heights:
  mod=f'JGk_TX2_Group{tree}_{h:02}'
  r=subprocess.run([sys.executable,str(P/'JGk_TX2_compile.py'),str(n),mod],stdout=(P/f'JGk_TX2_{n:03}-driver.log').open('w'),stderr=subprocess.STDOUT)
  print(n,mod,r.returncode,flush=True)
  if r.returncode:sys.exit(r.returncode)
  n+=1
