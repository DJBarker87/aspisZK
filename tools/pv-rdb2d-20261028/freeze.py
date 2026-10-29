from pathlib import Path
import json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';rows={}
for p in sorted(E.glob('lean-*/receipt.json')):
 j=json.loads(p.read_text())
 if j['exit']!=0:continue
 s=R/j['source_path']
 if not s.exists()or hashlib.sha256(s.read_bytes()).hexdigest()!=j['source_sha256']:continue
 rows[j['module']]=dict(module=j['module'],source_path=j['source_path'],source_sha256=j['source_sha256'],source_blob=j['source_blob'],attempt=j['attempt'])
(E/'frozen-proof-manifest.json').write_text(json.dumps(dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),modules=list(rows.values())),indent=2)+'\n')
print('frozen objects',len(rows))
