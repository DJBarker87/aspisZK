from pathlib import Path
import subprocess,json,lzma
E=Path(__file__).resolve().parent
code='''from pathlib import Path
import json,hashlib,shutil,lzma
b=Path('/home/dombarker/project-offloads/codex-cx-libc-20261111');src=Path('/home/dombarker/project-offloads/codex-cx-lib-20261111');rows=[]
assert shutil.disk_usage(b).free>=40_000_000_000
for source,dest in [('LIB_specs','LIBC_specs'),('LIB_objects','LIBC_base')]:
 for p in sorted((src/source).rglob('*')):
  if not p.is_file() or not any(str(p).endswith(t) for t in ['.olean','.olean.private','.olean.server','.ir']):continue
  q=b/dest/p.relative_to(src/source);q.parent.mkdir(parents=True,exist_ok=True)
  h=hashlib.sha256(p.read_bytes()).hexdigest()
  if not q.exists():shutil.copy2(p,q)
  assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  rows.append(dict(source=str(p),destination=str(q),sha256=h,bytes=q.stat().st_size))
x=json.loads(lzma.decompress((b/'LIBC_CACHE_IMPORTS.json.xz').read_bytes()));x['base_imports']=rows
(b/'LIBC_CACHE_IMPORTS.json.xz').write_bytes(lzma.compress(json.dumps(x).encode()));print(json.dumps(rows))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no','dombarker@100.108.41.90','python3'],input=code,text=True,capture_output=True)
(E/'LIBC_seed_base.log').write_text(r.stdout+r.stderr);assert r.returncode==0,r.stderr
(E/'LIBC_BASE_PINS.json').write_text(json.dumps(json.loads(r.stdout),indent=1)+'\n')
print('Pinned',len(json.loads(r.stdout)),'base objects')
