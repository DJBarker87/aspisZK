from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=[f'JGo_TX2_WeightRow{k}' for k in range(5)]+['JGo_TX2_WeightRows','JGo_TX2_WeightConstruct','JGo_TX2_WeightsTools','JGo_TX2_NewWeights','JGo_TX2_RoundCalls','JGo_TX2_MessageRead']
for n,m in enumerate(mods,59):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
print('Stop before070 for obstruction audit',flush=True)
