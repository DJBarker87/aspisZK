from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';rows={}
for p in E.glob('lean-*/receipt.json'):
 j=json.load(open(p))
 if j['exit']==0 and int(j['attempt'])<=60598:
  raw=(R/j['source_path']).read_bytes()
  if hashlib.sha256(raw).hexdigest()==j['source_sha256']:rows[j['module']]=dict(module=j['module'],source_path=j['source_path'],source_blob=j['source_blob'],source_sha256=j['source_sha256'],attempt=j['attempt'])
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(modules=list(rows.values()),authority='own exact successful source blobs; two canonical R72 dependencies follow EJR; external modules follow h4'),indent=2)+'\n')
print(len(rows),'modules frozen')
