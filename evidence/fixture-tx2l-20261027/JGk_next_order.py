from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGk_TX2_Positions0','JGk_TX2_Positions1','JGk_TX2_Positions2','JGk_TX2_KeyInjective','JGk_TX2_FrontierOrder0','JGk_TX2_FrontierOrder2','JGk_TX2_SiblingBase']
for n,mod in enumerate(mods,40):
 r=subprocess.run([sys.executable,str(P/'JGk_TX2_compile.py'),str(n),mod],stdout=(P/f'JGk_TX2_{n:03}-driver.log').open('w'),stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
