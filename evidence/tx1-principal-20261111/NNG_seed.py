from pathlib import Path
import json,hashlib,shutil
B=Path(__file__).resolve().parent
sources=json.loads((B/'NNG_SEED_REQUEST.json').read_text())
rows=[]
for item in sources:
 p=Path(item['path']); q=B/'NNG_seed'/'NMQ'/p.name
 q.parent.mkdir(parents=True,exist_ok=True)
 raw=p.read_bytes();h=hashlib.sha256(raw).hexdigest();assert h==item['sha256']
 if q.exists():assert q.read_bytes()==raw
 else:shutil.copyfile(p,q)
 rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=len(raw)))
(B/'NNG_SEED_PINS.json').write_text(json.dumps(rows,indent=1)+'\n')
print('Copied retained ledger25 export with verified hashes; predecessor paths remain read-only')
