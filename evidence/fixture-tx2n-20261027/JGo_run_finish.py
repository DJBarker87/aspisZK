from pathlib import Path
import subprocess,sys
P=Path(__file__).resolve().parent
mods=['JGo_TX2_WeightPointTail','JGo_TX2_StatementPoints']+[f'JGo_TX2_WeightRow{k}' for k in range(5)]+['JGo_TX2_WeightRows','JGo_TX2_WeightConstruct','JGo_TX2_NewWeights','JGo_TX2_RoundCalls','JGo_TX2_MessageRead']+[f'JGo_TX2_Message{k:02}' for k in range(0,64,8)]
for n,m in enumerate(mods,52):
 if n==71:
  print('OBSTRUCTION70 review required before attempt071',flush=True);sys.exit(70)
 with (P/f'JGo_TX2_{n:03}-driver.log').open('w') as out:
  p=subprocess.run([sys.executable,str(P/'JGo_TX2_compile.py'),str(n),m],stdout=out,stderr=subprocess.STDOUT)
 print(n,m,p.returncode,flush=True)
 if p.returncode:sys.exit(p.returncode)
