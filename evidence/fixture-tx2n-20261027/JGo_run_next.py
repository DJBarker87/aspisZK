from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
for n,m in [(41,'JGo_TX2_Round1'),(42,'JGo_TX2_LoopChain')]:
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  r=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
sys.exit(subprocess.run([sys.executable,str(P/'JGo_run_weights.py')]).returncode)
