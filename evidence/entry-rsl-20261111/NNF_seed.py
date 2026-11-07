from NNF_transport import *
import base64
admission('NNF_SEED')
expected={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (E.parent/'rowspec-lead-20261107').glob('*.lean') if p.name != 'RSL_Audit.lean'}
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path({B!r});rows=[]
for n in ['NNF_objects','NNF_generated','NNF_tmp','NNF_target']:(b/n).mkdir(exist_ok=True)
w=b.parent/'codex-cx-sound-int2-20261025'
for n in ['S2W_run_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:
 shutil.copy2(w/n,b/n)
 rows.append(dict(source=str(w/n),destination=str(b/n),sha256=hashlib.sha256((b/n).read_bytes()).hexdigest(),bytes=(b/n).stat().st_size))
for label,source in [('NLX','codex-cx-ledger8-cache-20261104/NLX_20261110/NLX_exports_20261110'),('NMW','codex-cx-entry-wrap-20261111/NMW_exports_20261111')]:
 src=b.parent/source;assert src.is_dir(),str(src)
 for p in src.rglob('*'):
  if not p.is_file():continue
  q=b/'NNF_seed'/label/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
expected=json.loads({json.dumps(expected)!r});src=b.parent/'codex-cx-stage-wrap-20261111'
for name,h in expected.items():
 p=src/'NMV_generated'/name
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h,('RSL SOURCE DRIFT',str(p))
 for p in (src/'NMV_objects').glob(name.removesuffix('.lean')+'.*'):
  assert p.suffix in ['.olean','.private','.server','.ir'],str(p)
  q=b/'NNF_seed'/'RSL'/p.name;q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  rows.append(dict(source=str(p),source_sha256=h,destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NNF_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NNF_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
