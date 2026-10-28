from NBW_host import *
import hashlib
admit('NBW_SETUP001')
payload={n:(E/n).read_text() for n in ['NBW_LAUNCHER_INPUTS.json','NBW_native.rs.txt','NBW_KMX_stubs.rs.txt']}
setup=f'''from pathlib import Path
import json,hashlib
b=Path({B!r});b.mkdir(exist_ok=True)
x=json.loads({json.dumps(json.dumps(payload))})
for n,s in json.loads(x['NBW_LAUNCHER_INPUTS.json']).items():
 p=b/n
 if not p.exists():p.write_text(s)
 else:assert p.read_text()==s
src=b/'NBW_src'
if not src.exists():src.symlink_to('/home/dombarker/project-offloads/codex-cx-native-query3-20261028/NBO_src',target_is_directory=True)
p=src/'crates/aspis-r1-cost-probe/src'
f=p/'candidate.rs';s=f.read_text();marker='\\n#[cfg(kani)] #[path="NBW_native.rs"] mod NBW_native;\\n'
if marker not in s:f.write_text(s+marker)
f=p/'lib.rs';s=f.read_text();marker='#![cfg_attr(kani, feature(allocator_api))]\\n'
if marker not in s:f.write_text(marker+s)
(p/'NBW_native.rs').write_text(x['NBW_native.rs.txt'])
(p/'KMX_stubs.rs').write_text(x['NBW_KMX_stubs.rs.txt'])
cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
pins={{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in cache.rglob('*') if p.is_file()}}
(b/'NBW_CACHE_START.json').write_text(json.dumps(pins,indent=2)+'\\n')
print(json.dumps(dict(cache_files=len(pins),scratch=str(src.resolve()),stubs_sha256=hashlib.sha256((p/'KMX_stubs.rs').read_bytes()).hexdigest())))
'''
for trial in range(11):
 r=subprocess.run(['ssh','-o','ConnectTimeout=15',H,'python3 -'],input=setup,capture_output=True,text=True)
 with (E/'NBW_SETUP_TRANSPORT.jsonl').open('a') as f:f.write(json.dumps(dict(trial=trial,exit=r.returncode,stderr=r.stderr))+'\n')
 if r.returncode!=255:break
 if trial<10:time.sleep(60)
assert r.returncode==0,r.stderr
(E/'NBW_SETUP.json').write_text(r.stdout)
r=py(f"from pathlib import Path;print((Path({B!r})/'NBW_CACHE_START.json').read_text())")
assert r.returncode==0
(E/'NBW_CACHE_START.json').write_text(r.stdout)
