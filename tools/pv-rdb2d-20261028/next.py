from pathlib import Path
import time,subprocess,sys,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
while not (E/'lean-61027/receipt.json').exists():
 if (E/'forest-queue.log').exists() and any(' 1\n' in x for x in (E/'forest-queue.log').read_text().splitlines(True)):raise RuntimeError('predecessor failure')
 time.sleep(5)
assert json.loads((E/'lean-61027/receipt.json').read_text())['exit']==0
for n,m in [(61028,'CollectorShape'),(61029,'CollectorTrace'),(61030,'CollectorProgram')]:
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as out:
   r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/lean.py'),str(n),'R1Z/PV_RDB2D_'+m],stdout=out,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:print('refusal',n,flush=True);time.sleep(180);continue
  break
 print(n,m,r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
