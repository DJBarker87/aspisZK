from NMW_transport import *
import base64
admission('NMW_S001')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path({B!r});rows=[]
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110')]:
 src=b.parent/source;assert src.is_dir(),str(src)
 for p in src.rglob('*'):
  if not p.is_file():continue
  q=b/'NMW_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['NMW_objects','NMW_generated','NMW_tmp','NMW_target']:(b/n).mkdir(exist_ok=True)
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
# Copy warm extraction objects privately. Never write the source cache.
src=b.parent/'codex-cx-slice-d-entry7-20261107/NIV_NHR_target';dst=b/'NMW_NHR_target'
if not dst.exists():shutil.copytree(src,dst)
for p in src.rglob('*'):
 if p.is_file():
  q=dst/p.relative_to(src);assert hashlib.sha256(p.read_bytes()).digest()==hashlib.sha256(q.read_bytes()).digest()
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMW_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMW_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
# Transport frozen payload/scripts only after admitted seed; all names are owned.
files={p.name:base64.b64encode(p.read_bytes()).decode() for p in E.glob('NMW_*') if p.is_file() and p.suffix in ['.py','.xz','.json','.sha256'] and p.name.startswith(('NMW_stage','NMW_FROZEN','NMW_STAGING','NMW_OPACITY'))}
r=ssh('python3',f'''from pathlib import Path
import base64,json
b=Path({B!r})
for n,t in json.loads({json.dumps(files)!r}).items():(b/n).write_bytes(base64.b64decode(t))
''');assert r.returncode==0,r.stderr
