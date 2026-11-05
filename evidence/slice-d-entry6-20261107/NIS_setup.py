from NIS_transport import *
import hashlib
admission('NIS_SEED')
nim=json.loads((E.parent/'owner-dedupe-20261107/NIM_EXPORT.json').read_text())
exports=[('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NIJ_exports_20261107_7c5f588b4380',None),(nim['export'],{Path(r['path']).name:r['sha256'] for r in nim['files']})]
r=ssh('python3',f'''from pathlib import Path
import shutil,hashlib,json
b=Path({B!r});assert not (b/'NIS_SEED.json').exists()
w=Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025')
for n in ['S2W_run_host.py','S2W_lean_host.py','lakefile.toml','lake-manifest.json','lean-toolchain']:shutil.copy2(w/n,b/n)
cache=Path('/home/dombarker/project-offloads/codex-cx-slice-d-entry-cache-20261104/NIS_seed_20261107');cache.mkdir(exist_ok=True)
rows=[]
for directory,pins in {exports!r}:
 for p in sorted(Path(directory).rglob('*')):
  if not p.is_file():continue
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if pins is not None:assert pins[p.name]==h
  dst=cache/p.relative_to(directory);dst.parent.mkdir(parents=True,exist_ok=True)
  if dst.exists():assert dst.read_bytes()==p.read_bytes()
  else:shutil.copy2(p,dst)
  rows.append(dict(source=str(p),path=str(dst),sha256=h,bytes=p.stat().st_size))
s=b/'NIS_src';assert not s.exists()
shutil.copytree('/home/dombarker/project-offloads/codex-cx-slice-d-entry5-20261107/NIJ_src',s,ignore=shutil.ignore_patterns('target','.git','__pycache__'))
for n in ['NIJ_src','NHY_src']:(b/n).symlink_to(s,target_is_directory=True)
for n in ['NIS_objects','NIS_tmp','NIS_native']:(b/n).mkdir(exist_ok=True)
x=dict(files=rows,seed_bytes=sum(r['bytes'] for r in rows),source_bytes=sum(p.stat().st_size for p in s.rglob('*') if p.is_file()),cache=str(cache),launchers={{n:hashlib.sha256((b/n).read_bytes()).hexdigest() for n in ['S2W_run_host.py','S2W_lean_host.py']}})
(b/'NIS_SEED.json').write_text(json.dumps(x,indent=1));print(json.dumps(x))
''')
assert r.returncode==0,r.stderr
(E/'NIS_SEED.json').write_text(r.stdout)
print(json.dumps({k:v for k,v in json.loads(r.stdout).items() if k!='files'}))
