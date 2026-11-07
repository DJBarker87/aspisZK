from NNE_transport import *
import base64
admission('NNE_S001')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path({B!r});rows=[]
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110'),('NMW','codex-cx-entry-wrap-20261111/NMW_exports_20261111'),('RSL','codex-cx-stage-wrap-20261111/NMV_RSL_objects')]:
 src=b.parent/source
 if not src.is_dir():
  if label=='RSL':continue
  raise RuntimeError(str(src))
 for p in src.rglob('*'):
  if not p.is_file():continue
  q=b/'NNE_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['NNE_objects','NNE_generated','NNE_tmp','NNE_target']:(b/n).mkdir(exist_ok=True)
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NNE_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NNE_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
