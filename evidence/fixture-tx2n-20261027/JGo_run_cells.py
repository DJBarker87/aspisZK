from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=[f'JGo_TX2_Cell{r}_{i}' for r in range(2) for i in range(7)][1:]
for n,m in enumerate(mods,10):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
