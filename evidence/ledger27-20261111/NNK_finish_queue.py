from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
assert (E/'NNK_L053/receipt.json').exists()and not(E/'NNK_CLIENT_ACTIVE').exists()
jobs=[(54,'lean','NNK_Review137'),(55,'lean','NNK_Review087'),(56,'lean','NNK_Review234'),(57,'lean','NNK_OwnerStatements'),(58,'audit','scan'),(59,'audit','close'),(60,'audit','verify-retention')]
for n,k,t in jobs:
 a=f'NNK_L{n:03}';p=E/a/'receipt.json'
 if p.exists():
  r=json.loads(p.read_text());assert r['exit_status']==0 and r['module']==t;print(a,'retained; no rerun',flush=True);continue
 with(E/(a+'-client.log')).open('w')as f:r=subprocess.run([sys.executable,str(E/'NNK_run.py'),a,k,t],stdout=f,stderr=subprocess.STDOUT)
 print(a,t,r.returncode,flush=True)
 # Never rerun a failed source shape. Inventory/client repairs, if needed, use a new named attempt.
 if r.returncode:sys.exit(r.returncode)
