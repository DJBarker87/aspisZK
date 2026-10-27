from pathlib import Path
import json,sys,subprocess
P=Path(__file__).resolve().parent
mods=json.loads((P/'JGm_LEVEL_MODULES.json').read_text())
# Smallest affected pair/control case is preflighted separately in 025.
mods=[x for x in mods if x not in ['JGm_TX2_Level0_00','JGm_TX2_Level0_11']]
for n,mod in enumerate(mods,26):
 if n>=70:break
 with (P/f'JGm_TX2_{n:03}-driver.log').open('w') as out:
  r=subprocess.run([sys.executable,str(P/'JGm_TX2_compile.py'),str(n),mod],stdout=out,stderr=subprocess.STDOUT)
 print(n,mod,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
