from pathlib import Path
import time,subprocess,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';p=E/'lean-60592/receipt.json'
while not p.exists():time.sleep(5)
assert json.loads(p.read_text())['exit']==0
for script,n,module in [('canonical-lean.py',60593,'AspisR72Sampler/Types'),('lean.py',60594,'R1Z/PV_RDB2C_SamplerInstance'),('lean.py',60595,'R1Z/PV_RDB2C_WeightsInstance'),('lean.py',60596,'R1Z/PV_RDB2C_R1SamplerLongDivision')]:
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as f:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028'/script),str(n),module],stdout=f,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:print('refusal',n,'cooldown 180 seconds',flush=True);time.sleep(180);continue
  break
 print(n,module,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
