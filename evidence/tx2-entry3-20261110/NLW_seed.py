from NLW_transport import *
import shutil,hashlib
admission('NLW_S001')
r=ssh('python3',f"""from pathlib import Path
import json,hashlib,shutil
b=Path({B!r});rows=[]
for label,source in [('NLM','codex-cx-tx2-entry2-20261110/NLM_exports_20261110_559dd822c508'),('NLF','codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014'),('NLS','codex-cx-ledger8-cache-20261104/NLS_20261110/NLS_exports_20261110')]:
 src=b.parent/source;assert src.is_dir(),src
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=b/'NLW_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert hashlib.sha256(q.read_bytes()).digest()==hashlib.sha256(p.read_bytes()).digest()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
for n in ['NLW_objects','NLW_generated','NLW_tmp','NLW_target']:(b/n).mkdir(exist_ok=True)
shutil.copy2(b.parent/'codex-cx-tx2-entry-20261109/S2W_run_host.py',b/'S2W_run_host.py')
x=dict(files=rows,bytes=sum(z['bytes'] for z in rows));(b/'NLW_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
""")
assert r.returncode==0,r.stderr
(E/'NLW_SEED.json').write_text(r.stdout)
x=json.loads(r.stdout);print(json.dumps(dict(files=len(x['files']),bytes=x['bytes'])))
