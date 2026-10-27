from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGk_TX2_Scratch0','JGk_TX2_Scratch1','JGk_TX2_Scratch2']
for n,mod in enumerate(mods,60):
 r=subprocess.run([sys.executable,str(P/'JGk_TX2_compile.py'),str(n),mod],stdout=(P/f'JGk_TX2_{n:03}-driver.log').open('w'),stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
