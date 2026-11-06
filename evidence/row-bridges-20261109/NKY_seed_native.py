from NKY_transport import *
admission('NKY_native_seed')
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-tx2-adapters2-20261108/NKP_src');dst=b/'NKY_src'
rows=[]
for p in src.rglob('*'):
 if not p.is_file() or p.is_symlink():continue
 q=dst/p.relative_to(src);q.parent.mkdir(parents=True,exist_ok=True)
 # Unchanged base files only; uploaded authored inputs are retained.
 if not q.exists():shutil.copy2(p,q)
 rows.append(dict(source=str(p),relative=str(p.relative_to(src)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
print(json.dumps(dict(files=rows,bytes=sum(r['bytes']for r in rows))))
''');assert r.returncode==0,r.stderr
(E/'NKY_NATIVE_SEED.json.xz').write_bytes(__import__('lzma').compress(r.stdout.encode()))
print('native source seed copied; hashes recorded')
