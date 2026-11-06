from NJH_transport import *
admission('NJH_NATIVE_SEED')
r=ssh('python3',f"""from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});source=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry8-20261107/NJD_src');s=b/'NJH_src';assert not s.exists()
shutil.copytree(source,s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NIJ_src','NHY_src']:(b/n).symlink_to(s,target_is_directory=True)
print(json.dumps(dict(source=str(source),bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),lock_sha256=hashlib.sha256((s/'Cargo.lock').read_bytes()).hexdigest(),free_bytes=shutil.disk_usage(b).free)))
""")
assert r.returncode==0,r.stderr
(E/'NJH_NATIVE_SEED.json').write_text(r.stdout)
print('Owned native scratch copied; target remains NJH_target')
