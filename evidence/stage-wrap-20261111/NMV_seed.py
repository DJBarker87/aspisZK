from NMV_transport import *
import base64
admission('NMV_S001')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib,lzma,base64
b=Path({B!r});rows=[]
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110'),('NMN','codex-cx-tx2-entry5-20261110/NMN_exports_20261110')]:
 src=b.parent/source;assert src.is_dir(),str(src)
 for p in sorted(src.rglob('*')):
  if not p.is_file():continue
  q=b/'NMV_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['NMV_objects','NMV_generated','NMV_tmp','NMV_target']:(b/n).mkdir(exist_ok=True)
shutil.copy2(b.parent/'codex-cx-sound-int2-20261025/S2W_run_host.py',b/'S2W_run_host.py')
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMV_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMV_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
