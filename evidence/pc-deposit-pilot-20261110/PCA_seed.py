from PCA_transport import *
import hashlib
admission('PCA_SEED')
r=ssh('python3',f'''from pathlib import Path
import json,shutil,hashlib
b=Path({B!r}); records=[]
selections=[('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109/NLF_exports_20261109_72e6c5ce1014','NLF_', 'NLF_seed'),('/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NIZ_exports_20261107','NIZ_', 'NIZ_seed'),('/home/dombarker/project-offloads/codex-cx-pool-prefix-cache-20261104/NIO_exports_20261107','NIO_', 'NIO_seed'),('/home/dombarker/project-offloads/codex-cx-ledger8-cache-20261104/NLG_20261110/NLG_exports_20261110','NLG_', 'NLG_seed')]
for root,prefix,target in selections:
 for p in Path(root).rglob('*'):
  if not p.is_file() or not p.name.startswith(prefix):continue
  # These exports consist of the supporting import packets; no corpus copy.
  q=b/target/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  records.append(dict(source=str(p),target=str(q),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
s=Path('/home/dombarker/project-offloads/codex-cx-sdk-borrow-20261109')
for n in ['S2W_lean_host.py','S2W_run_host.py','lean-toolchain','lakefile.toml','lake-manifest.json']:
 q=b/n
 if q.exists():assert q.read_bytes()==(s/n).read_bytes()
 else:shutil.copy2(s/n,q)
 records.append(dict(source=str(s/n),target=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),bytes=q.stat().st_size))
for n in ['PCA_objects','PCA_tmp','PCA_generated']:(b/n).mkdir(exist_ok=True)
print(json.dumps(dict(files=records,free_bytes=shutil.disk_usage(b).free)))
''')
assert r.returncode==0,r.stderr
(E/'PCA_SEED.json').write_text(r.stdout)
print('Selected retained support packets copied privately and individually hashed; no host scope launched.')
