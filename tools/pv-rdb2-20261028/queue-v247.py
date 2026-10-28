"""One smallest module per charged attempt; stop at the first proof error."""
from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2-20261028'
j=json.loads((E/'V247-owned-cone.json').read_text())
start=int(sys.argv[1]) if len(sys.argv)>1 else 0
for offset,module in enumerate(j['order'][start:],start):
 n=41142+offset
 assert 41142<=n<=41150
 assert not (E/f'lean-{n}/receipt.json').exists()
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as log:
   r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2-20261028/lean.py'),str(n),module.replace('.','/')],stdout=log,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:
   print('REFUSED',n,'cooldown180s',flush=True);time.sleep(180);continue
  break
 print(n,module,'exit',r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
