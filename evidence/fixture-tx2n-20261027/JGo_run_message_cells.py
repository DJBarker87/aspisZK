from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=[f'JGo_TX2_Message{k:02}' for k in range(0,64,8)]+['JGo_TX2_FinishPrefixTools','JGo_TX2_FinishPrefix']
for n,m in enumerate(mods,80):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
