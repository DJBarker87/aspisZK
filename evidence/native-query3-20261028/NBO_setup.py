from NBO_host import *
import hashlib
admit('NBO_SETUP001')
r=py('''from pathlib import Path
import json,hashlib,shutil
b=Path('/home/dombarker/project-offloads/codex-cx-native-query3-20261028');old=Path('/home/dombarker/project-offloads/codex-cx-native-query2-20261027')
for n in ['S2W_lean_host.py','S2W_run_host.py','lakefile.toml','lean-toolchain','lake-manifest.json']:
 assert not (b/n).exists();shutil.copyfile(old/n,b/n)
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028');assert not cache.exists();cache.mkdir()
source=Path('/home/dombarker/project-offloads/codex-cx-leaf-cache-20261027')
imports={}
for p in source.rglob('*'):
 if p.is_file():
  q=cache/p.relative_to(source);q.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,q)
  h=hashlib.sha256(p.read_bytes()).hexdigest();assert hashlib.sha256(q.read_bytes()).hexdigest()==h
  imports[str(q)]=dict(source=str(p),sha256=h,bytes=q.stat().st_size)
(b/'NBO_CACHE_START.json').write_text(json.dumps(imports,indent=2)+'\\n')
print(json.dumps(dict(objects=len(imports))))
''')
assert r.returncode==0,r.stderr
r=py("from pathlib import Path;print(Path('/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_CACHE_START.json').read_text())")
assert r.returncode==0
(E/'NBO_CACHE_START.json').write_text(r.stdout)
