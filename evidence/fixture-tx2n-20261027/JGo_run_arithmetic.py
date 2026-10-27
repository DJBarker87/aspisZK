from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGo_TX2_ArithmeticPreflight']+[f'JGo_TX2_Horner{r}_{i}' for r in range(2) for i in range(7)]+['JGo_TX2_Round0','JGo_TX2_Round1','JGo_TX2_LoopChain']
for n,m in enumerate(mods,23):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
