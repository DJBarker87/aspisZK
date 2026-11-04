from pathlib import Path
import shutil,json,hashlib
P=Path('/home/dombarker/project-offloads');s=P/'codex-cx-slice-d-field-20261104/NFT_src';d=P/'codex-cx-slice-d-field2-20261104/NGA_src'
shutil.copytree(s,d,dirs_exist_ok=True,ignore=shutil.ignore_patterns('.git','target'))
lock=d/'Cargo.lock'
print(json.dumps(dict(source=str(s),destination=str(d),lock_sha256=hashlib.sha256(lock.read_bytes()).hexdigest(),mode='copy retained immutable predecessor scratch; only NGA cfg(kani) overlays follow')))
