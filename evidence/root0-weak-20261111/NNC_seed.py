from NNC_transport import *
import shutil,hashlib
admission('NNC_S001')
r=ssh('python3',f"""from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});rows=[]
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110'),('NMN','codex-cx-tx2-entry5-20261110/NMN_exports_20261110'),('NMF','codex-cx-root-transport-20261110/NMF_exports_20261110')]:
 src=b.parent/source;assert src.is_dir(),src
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=b/'NNC_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert hashlib.sha256(q.read_bytes()).digest()==hashlib.sha256(p.read_bytes()).digest()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
for n in ['NNC_objects','NNC_generated','NNC_tmp']:(b/n).mkdir(exist_ok=True)
shutil.copy2(b.parent/'codex-cx-tx2-entry-20261109/S2W_run_host.py',b/'S2W_run_host.py')
x=dict(files=rows,bytes=sum(z['bytes'] for z in rows));(b/'NNC_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
""")
assert r.returncode==0,r.stderr
(E/'NNC_SEED.json').write_text(r.stdout)
x=json.loads(r.stdout);print(json.dumps(dict(files=len(x['files']),bytes=x['bytes'])))
