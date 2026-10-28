from NBZ_host import *
import hashlib
admit('NBZ_SETUP001')
payload=json.loads((E/'NBZ_LAUNCHER_INPUTS.json').read_text())
code=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});b.mkdir(exist_ok=True)
for n,s in {payload!r}.items():
 p=b/n
 if not p.exists():p.write_text(s)
 else:assert p.read_text()==s
src=b/'NBZ_src'
if not src.exists():src.symlink_to('/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_src',target_is_directory=True)
p=src/'crates/aspis-r1-cost-probe/src';f=p/'candidate.rs';s=f.read_text();marker='\\n#[cfg(kani)] #[path="NBZ_native.rs"] mod NBZ_native;\\n'
if marker not in s:f.write_text(s+marker)
assert hashlib.sha256((p/'KMX_stubs.rs').read_bytes()).hexdigest()=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
(b/'NBZ_CACHE_START.json').write_text(json.dumps(pins,indent=2)+'\\n')
print(json.dumps(dict(cache_files=len(pins),scratch=str(src.resolve()))))
'''
r=py(code);assert r.returncode==0,r.stderr
(E/'NBZ_SETUP.json').write_text(r.stdout)
# Admission precedes upload. No second corpus or cache is created.
for trial in range(11):
 r=subprocess.run(['scp','-o','ConnectTimeout=15','/tmp/NBZ_native.rs',H+':'+B+'/NBZ_src/crates/aspis-r1-cost-probe/src/NBZ_native.rs'],capture_output=True,text=True)
 with (E/'NBZ_SETUP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
r=py(f"from pathlib import Path;print((Path({B!r})/'NBZ_CACHE_START.json').read_text())");assert r.returncode==0
(E/'NBZ_CACHE_START.json').write_text(r.stdout)
