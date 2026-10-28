from NCG_host import *
admit('NCG_SETUP001')
payload=json.loads((E/'NCG_LAUNCHER_INPUTS.json').read_text())
r=py(f'''from pathlib import Path
import json,hashlib
b=Path({B!r});b.mkdir(exist_ok=True)
for n,s in {payload!r}.items():
 p=b/n
 if not p.exists():p.write_text(s)
 else:assert p.read_text()==s
src=b/'NCG_src'
if not src.exists():src.symlink_to('/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_src',target_is_directory=True)
p=src/'crates/aspis-r1-cost-probe/src';f=p/'candidate.rs';s=f.read_text();marker='\\n#[cfg(kani)] #[path="NCG_native.rs"] mod NCG_native;\\n'
if marker not in s:f.write_text(s+marker)
assert hashlib.sha256((p/'KMX_stubs.rs').read_bytes()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
(b/'NCG_CACHE_START.json').write_text(json.dumps(pins,indent=2)+'\\n')
print(json.dumps(dict(cache_files=len(pins),scratch=str(src.resolve()))))
''');assert r.returncode==0,r.stderr
(E/'NCG_SETUP.json').write_text(r.stdout)
r=py(f"from pathlib import Path;print((Path({B!r})/'NCG_CACHE_START.json').read_text())");assert r.returncode==0
(E/'NCG_CACHE_START.json').write_text(r.stdout)
