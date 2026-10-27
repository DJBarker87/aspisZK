from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
for n,h in enumerate(range(10,18),71):
 mod=f'JGm_TX2_Level2_{h:02}'
 with (P/f'JGm_TX2_{n:03}-driver.log').open('w') as out:
  r=subprocess.run([sys.executable,str(P/'JGm_TX2_compile.py'),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
