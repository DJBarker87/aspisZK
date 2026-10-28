from NCJ_host import *
import io,tarfile
admit('NCJ_SETUP002')
launchers=json.loads((E/'NCJ_LAUNCHER_INPUTS.json').read_text())
r=py(f'''from pathlib import Path
import shutil,json,hashlib
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-tx2weights-cache-20261028')
assert not cache.exists(),'private cache already exists; inspect instead of overwrite'
cache.mkdir();pins=[]
for name in ['codex-cx-leaf-cache-20261027','codex-cx-tx2mid-cache-20261028']:
 root=Path('/home/dombarker/project-offloads')/name
 for p in root.rglob('*'):
  if p.is_file():
   rel=p.relative_to(root);q=cache/rel;q.parent.mkdir(parents=True,exist_ok=True);shutil.copy2(p,q)
   pins.append(dict(source=str(p),relative=str(rel),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size))
(b/'NCJ_IMPORTED_CACHE.json').write_text(json.dumps(pins,indent=2)+'\\n')
for name,s in {launchers!r}.items():(b/name).write_text(s)
(b/'NCJ_src').mkdir();(b/'NCJ_tmp').mkdir()
print(json.dumps(dict(imported=len(pins),bytes=sum(p['bytes'] for p in pins))))
''');assert r.returncode==0,r.stderr;print(r.stdout)
# Read-only source extraction from immutable frozen revision, never another worktree.
paths=['Cargo.toml','Cargo.lock','crates','programs']
blob=subprocess.check_output(['git','archive','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',*paths])
r=subprocess.run(['ssh',H,'tar -xf - -C '+shlex.quote(B+'/NCJ_src')],input=blob,capture_output=True);assert r.returncode==0,r.stderr
r=py(f'''from pathlib import Path
import hashlib,json
b=Path({B!r});s=b/'NCJ_src'
print(json.dumps(dict(cache=json.loads((b/'NCJ_IMPORTED_CACHE.json').read_text()),sources={{str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in s.rglob('*') if p.is_file()}})))
''');assert r.returncode==0,r.stderr
x=json.loads(r.stdout)
(E/'NCJ_IMPORTED_CACHE.json').write_text(json.dumps(x['cache'],indent=2)+'\n')
(E/'NCJ_FROZEN_SOURCES.json').write_text(json.dumps(x['sources'],indent=2)+'\n')
