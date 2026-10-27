from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGm_TX2_Initial','JGm_TX2_Valid','JGm_TX2_Levels','JGm_TX2_Verify','JGm_TX2_PaddingCalls','JGm_TX2_Terminal','JGm_TX2_Batch']
for n,mod in enumerate(mods,79):
 with (P/f'JGm_TX2_{n:03}-driver.log').open('w') as out:
  r=subprocess.run([sys.executable,str(P/'JGm_TX2_compile.py'),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
