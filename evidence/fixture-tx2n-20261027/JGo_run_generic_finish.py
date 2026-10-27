from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGo_TX2_StatementPoints']+[f'JGo_TX2_WeightRow{k}' for k in range(5)]+['JGo_TX2_WeightRows','JGo_TX2_WeightConstruct','JGo_TX2_WeightsTools','JGo_TX2_NewWeights','JGo_TX2_RoundCalls','JGo_TX2_MessageRead']+[f'JGo_TX2_Message{k:02}' for k in range(0,24,8)]
for n,m in enumerate(mods,55):
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
print('Stop before attempt070 for mandatory obstruction audit',flush=True)
