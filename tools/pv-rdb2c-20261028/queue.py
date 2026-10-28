from pathlib import Path
import subprocess,json,sys,time
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028'
rows=json.loads((E/sys.argv[1]).read_text());start=int(sys.argv[2])
for i,row in enumerate(rows):
 n=start+i
 with (E/f'{n}-driver.log').open('a') as f:r=subprocess.run([sys.executable,str(R/'tools/pv-rdb2c-20261028/lean.py'),str(n),row['module']],stdout=f,stderr=subprocess.STDOUT)
 print(n,row['module'],r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
