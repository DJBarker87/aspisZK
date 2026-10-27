from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
for n,m in [(97,'JGo_TX2_OuterRoot'),(98,'JGo_TX2_Powers0'),(99,'JGo_TX2_Powers1')]:
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
