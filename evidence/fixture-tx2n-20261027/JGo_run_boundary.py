from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGo_TX2_FinishPrefix','JGo_TX2_Partial','JGo_TX2_PairGuard','JGo_TX2_Powers0','JGo_TX2_Powers1','JGo_TX2_PowersK']
for n,m in enumerate(mods,90):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
