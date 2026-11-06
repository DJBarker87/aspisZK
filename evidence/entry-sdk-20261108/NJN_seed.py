from NJN_transport import *
import hashlib,lzma
admission('NJN_SEED')
r=ssh('python3',f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});rows=[];sizes=[]
seeds=['/home/dombarker/project-offloads/codex-cx-slice-d-prepared-cache-20261104/NJH_exports_20261107_5c559aa7a326','/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NIV_exports_20261107_092332c4a1ed']
for root in seeds:
 root=Path(root);size=0
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  q=b/'NJN_seed'/p.relative_to(root);q.parent.mkdir(parents=True,exist_ok=True)
  if q.exists():assert q.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,q)
  size+=p.stat().st_size;rows.append(dict(source=str(p),target=str(q),bytes=p.stat().st_size,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
 sizes.append(dict(seed=str(root),bytes=size))
s=Path('/home/dombarker/project-offloads/codex-cx-entry-leaves-20261107')
for n in ['S2W_lean_host.py','S2W_run_host.py','lean-toolchain','lakefile.toml','lake-manifest.json']:shutil.copy2(s/n,b/n)
for n in ['NJN_objects','NJN_tmp']:(b/n).mkdir(exist_ok=True)
print(json.dumps(dict(seeds=sizes,files=rows,free_bytes=shutil.disk_usage(b).free)))
''')
assert r.returncode==0,r.stderr
(E/'NJN_SEED.json').write_text(r.stdout)
print('NJN seed copied with individual hashes; launchers unchanged')
