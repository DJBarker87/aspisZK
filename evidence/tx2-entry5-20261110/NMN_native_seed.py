from NMN_transport import *
import base64
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib,lzma,base64
b=Path({B!r});src=b.parent/'codex-cx-tx2-entry4-20261110';rows=[]
for p in sorted((src/'NMK_src').rglob('*')):
 if not p.is_file() or 'target' in p.parts:continue
 rel=p.relative_to(src/'NMK_src');q=b/'NMN_src'/rel;q.parent.mkdir(parents=True,exist_ok=True)
 if q.exists():assert q.read_bytes()==p.read_bytes()
 else:shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for old,new in [('NMK_FROZEN_PINS.json','NMN_FROZEN_PINS.json'),('NMK_EXTRA_PINS.json','NMN_EXTRA_PINS.json'),('NMK_KMX_copy_stubs.patch','NMN_KMX_copy_stubs.patch')]:shutil.copy2(src/old,b/new)
shutil.copy2(b/'NMN_KMX_copy_stubs.patch',b/'NMN_expected_KMX.patch')
raw=json.dumps(rows).encode();print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(lzma.compress(raw)).decode())))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NMN_NATIVE_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NMN_NATIVE_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
