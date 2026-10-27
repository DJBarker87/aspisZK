from pathlib import Path
import json,subprocess,sys
P=Path(__file__).resolve().parent
n=int(sys.argv[1]);offset=int(sys.argv[2]);limit=int(sys.argv[3])
for row in json.loads((P/'JGc_HASH_PLAN.json').read_text())[offset:limit]:
 assert n<=69,'Stop before mandatory OBSTRUCTION70 audit'
 with (P/f'JGc_TX2_{n:03}-driver.log').open('w') as f:
  r=subprocess.run([sys.executable,str(P/'JGc_TX2_compile.py'),str(n),row['module']],stdout=f,stderr=subprocess.STDOUT)
 print(n,row['module'],r.returncode,flush=True)
 if r.returncode:sys.exit(r.returncode)
 n+=1
