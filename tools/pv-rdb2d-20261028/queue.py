from pathlib import Path
import subprocess,json,sys,time,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028'
rows=json.loads((E/sys.argv[1]).read_text());start=int(sys.argv[2])
for i,row in enumerate(rows):
 n=start+i
 receipt=E/f'lean-{n}/receipt.json'
 if receipt.exists():
  j=json.loads(receipt.read_text());source=R/'docs/research/v8-r0-zk-20261009/lean'/(row['module']+'.lean')
  assert j['exit']==0 and j['module']==row['module'] and j['source_sha256']==hashlib.sha256(source.read_bytes()).hexdigest()
  print('reuse completed exact-source attempt',n,flush=True);continue
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as f:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2d-20261028/lean.py'),str(n),row['module']],stdout=f,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:
   print('REFUSAL',n,'cooldown 180 seconds, same unlaunched ID',flush=True);time.sleep(180);continue
  break
 print(n,row['module'],r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
