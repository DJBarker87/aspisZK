from NBZ_host import *
import hashlib,base64,zlib
frozen=json.loads((E/'NBZ_LOCAL_FREEZE.json').read_text())
payload=base64.b64encode(zlib.compress(json.dumps(frozen['entries']).encode())).decode()
code=f'''from pathlib import Path
import json,hashlib,base64,zlib,re
b=Path({B!r});cache=Path('/home/dombarker/project-offloads/codex-cx-query-cache-20261028');src=b/'NBZ_src'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for part in iter(lambda:f.read(1048576),b''):h.update(part)
 return h.hexdigest()
initial=json.loads((b/'NBZ_CACHE_START.json').read_text());changed=[]
for n,v in initial.items():
 p=Path(n)
 if not p.exists() or sha(p)!=v['sha256']:changed.append(n)
assert not changed,changed
roots=[cache,Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025'),Path('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')]
prior=json.loads(Path('/home/dombarker/project-offloads/codex-cx-native-query4-20261028/NBW_LIBRARY_PIN.json').read_text());resolution={{}}
for n,v in prior.items():
 rel=Path(n).relative_to('/home/dombarker/project-offloads/codex-cx-sound-int2-20261025/objects')
 p=next(root/rel for root in roots if (root/rel).is_file());assert sha(p)==v['sha256'],str(rel)
 resolution[str(rel)]=dict(path=str(p),sha256=sha(p))
entries=json.loads(zlib.decompress(base64.b64decode({payload!r})));mismatches=[];qualified=[]
for row in entries:
 p=src/row['path'];data=p.read_bytes()
 if row['path']=='crates/aspis-r1-cost-probe/src/candidate.rs':
  data=re.sub(rb'\\n#\\[cfg\\(kani\\)\\] #\\[path="NBZ_[^"]+\\.rs"\\] mod NBZ_[A-Za-z0-9_]+;\\n',b'',data)
  # Now byte-identical to the inherited NBW terminal candidate pin.
  assert hashlib.sha256(data).hexdigest()=='7e51f020af888e6c74ad92932887efacd03e485619ba1fe9350406a9c6936023'
  qualified.append(dict(path=row['path'],qualification='only own NBZ cfg registrations removed; inherited NBW terminal bytes match'))
 elif row['path']=='crates/aspis-r1-cost-probe/src/lib.rs':
  assert sha(p)=='04db82c4b8b5d9e46688b1d28f1ad9933b4598e1e144b10dd7cd642b36ab1c87'
  qualified.append(dict(path=row['path'],qualification='unchanged inherited cfg allocator_api/recursion attributes'))
 elif row['path']=='crates/aspis-r1-cost-probe/src/verifier.rs':
  assert sha(p)=='23c3de16ed408fadfa74d4597345b00da7285ee7b5c5df0058eb4dc6fb65d569'
  qualified.append(dict(path=row['path'],qualification='unchanged inherited NBF/NBO cfg harness registrations'))
 elif hashlib.sha256(data).hexdigest()!=row['sha256']:mismatches.append(row['path'])
assert not mismatches,mismatches
assert sha(src/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(src/'crates/aspis-r1-cost-probe/src/KMX_stubs.rs')=='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'
new={{str(p):dict(sha256=sha(p),bytes=p.stat().st_size) for p in cache.glob('NBZ_*') if p.is_file()}}
print(json.dumps(dict(imported_cache_files=len(initial),changed_imports=changed,aeneas_resolution=resolution,new_objects=new,frozen_files=len(entries),scratch_mismatches=mismatches,qualified_inherited=qualified,cache_retained=True),indent=2))
'''
r=py(code);assert r.returncode==0,r.stderr
(E/'NBZ_HOST_PIN.json').write_text(r.stdout)
print('Pinned imported objects, actual Aeneas resolution and frozen scratch source')
