from NJY_transport import *
admission('NJY_P002')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});src=Path('/home/dombarker/project-offloads/codex-cx-tx2-decoders2-20261107/NIJ_src');dst=b/'NIJ_src'
assert not dst.exists()
size=sum(p.stat().st_size for p in src.rglob('*') if p.is_file() and 'target' not in p.relative_to(src).parts)
assert shutil.disk_usage(b).free > size+3*1024**3
shutil.copytree(src,dst,ignore=shutil.ignore_patterns('target','__pycache__'))
lock=dst/'Cargo.lock';print(json.dumps(dict(source=str(src),destination=str(dst),bytes=size,lock_sha256=hashlib.sha256(lock.read_bytes()).hexdigest(),free_bytes=shutil.disk_usage(b).free)))
(b/'NJY_tmp').mkdir(exist_ok=True)
''');assert r.returncode==0,r.stderr
(E/'NJY_RUST_SEED.json').write_text(r.stdout);print(r.stdout.strip())
