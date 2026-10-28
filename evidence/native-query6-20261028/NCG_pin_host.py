from NCG_host import *
r=py(f'''from pathlib import Path
import hashlib,json,re
b=Path({B!r});src=b/'NCG_src';cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
initial=json.loads((b/'NCG_CACHE_START.json').read_text());changed=[n for n,v in initial.items() if not Path(n).exists() or sha(Path(n))!=v['sha256']]
assert not changed,changed
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
prior=json.loads(Path('/home/dombarker/project-offloads/codex-cx-native-query4-20261028/NBW_LIBRARY_PIN.json').read_text());resolution={{}}
for n,v in prior.items():
 rel=Path(n).relative_to('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects');p=next(root/rel for root in roots if (root/rel).is_file());assert sha(p)==v['sha256'];resolution[str(rel)]=dict(path=str(p),sha256=sha(p))
new={{str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in cache.glob('NCG_*') if p.is_file()}}
print(json.dumps(dict(imported_cache_files=len(initial),changed_imports=changed,aeneas_resolution=resolution,new_objects=new,cache_retained=True,lock_sha256=sha(src/'Cargo.lock'),KMX_payload_sha256=sha(src/'crates/aspis-r1-cost-probe/src/KMX_stubs.rs')),indent=2))
''');assert r.returncode==0,r.stderr
(E/'NCG_HOST_PIN.json').write_text(r.stdout)
