from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028'
rows=json.loads((E/sys.argv[1]).read_text());start=int(sys.argv[2])
for i,row in enumerate(rows):
 n=start+i
 for retry in range(11):
  with (E/f'{n}-driver.log').open('a') as f:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028/lean.py'),str(n),row['module']],stdout=f,stderr=subprocess.STDOUT)
  if r.returncode==78 and retry<10:
   print('REFUSAL',n,'cooldown 180 seconds, same unlaunched ID',flush=True);time.sleep(180);continue
  break
 print(n,row['module'],r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
