from NJD_transport import *
import hashlib
admission('NJD_SEED')
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});assert not (b/'NJD_SEED.json').exists()
w=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry7-20261107')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
src=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NIV_exports_20261107_092332c4a1ed')
cache=b/'NJD_seed';cache.mkdir(exist_ok=True);rows=[]
for p in sorted(src.rglob('*')):
 if not p.is_file():continue
 dst=cache/p.relative_to(src);dst.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,dst)
 rows.append(dict(source=str(p),path=str(dst),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
s=b/'NJD_src';assert not s.exists();shutil.copytree(w/'NIV_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NIJ_src','NHY_src']:(b/n).symlink_to(s,target_is_directory=True)
for n in ['NJD_objects','NJD_tmp','NJD_native']:(b/n).mkdir(exist_ok=True)
x=dict(files=rows,seed_bytes=sum(r['bytes'] for r in rows),source_bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),cache=str(cache),free_bytes=shutil.disk_usage(b).free,launchers={{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in ['S2W_run_host.py','S2W_lean_host.py']}})
(b/'NJD_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
''')
assert r.returncode==0,r.stderr
(E/'NJD_SEED.json').write_text(r.stdout)
x=json.loads(r.stdout);expected=json.loads((E.parent/'slice-d-entry7-20261107/NIV_EXPORT.json').read_text())
objects=[z for z in x['files'] if z['path'].endswith('.olean')]
assert sum(z['bytes'] for z in objects)==expected['bytes']
assert [(Path(z['path']).name,z['sha256']) for z in objects]==[(z['path'],z['sha256']) for z in expected['files']]
print(json.dumps({k:v for k,v in x.items() if k!='files'}))
