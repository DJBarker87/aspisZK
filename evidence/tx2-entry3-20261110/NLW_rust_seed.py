from NLW_transport import *
import hashlib,lzma,base64
admission('NLW_S004')
r=ssh('python3',f'''from pathlib import Path
import json,hashlib,shutil,lzma,base64
b=Path({B!r});src=b.parent/'codex-cx-tx2-entry2-20261110/NLM_target';dst=b/'NLW_target';rows=[]
assert src.is_dir()
for p in sorted(src.rglob('*')):
 if not p.is_file() or p.is_symlink():continue
 q=dst/p.relative_to(src)
 if q.exists():continue
 q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
 rows.append(dict(source=str(p),destination=str(q),bytes=q.stat().st_size,sha256=hashlib.sha256(q.read_bytes()).hexdigest()))
raw=json.dumps(rows).encode();z=lzma.compress(raw);(b/'NLW_RUST_SEED.json.xz').write_bytes(z)
print(json.dumps(dict(files=len(rows),bytes=sum(x['bytes'] for x in rows),sha256=hashlib.sha256(raw).hexdigest(),archive=base64.b64encode(z).decode())))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);(E/'NLW_RUST_SEED.json.xz').write_bytes(base64.b64decode(x.pop('archive')));(E/'NLW_RUST_SEED.json.sha256').write_text(x['sha256']+'\n');print(json.dumps(x))
