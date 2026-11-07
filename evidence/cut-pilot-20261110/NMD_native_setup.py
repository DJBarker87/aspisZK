"""Restore immutable frozen corpus privately; no shared target writes."""
from NMD_transport import *
import lzma,base64,hashlib
archive=E.parent/'sdk-borrow-20261109/NLF_FROZEN_INPUTS.json.xz'
admission('NMD_S002')
payload=base64.b64encode(archive.read_bytes()).decode()
r=ssh('python3',f'''from pathlib import Path
import lzma,base64,json,hashlib,shutil
b=Path({B!r});x=json.loads(lzma.decompress(base64.b64decode({payload!r})));rows=[]
for n,v in x.items():
 dest=n.replace('NLF_src/','NMD_src/').replace('NLF_FROZEN_PINS','NMD_FROZEN_PINS').replace('NLF_KMX','NMD_KMX')
 raw=base64.b64decode(v) if n.startswith('NLF_src/') else v.encode()
 p=b/dest;p.parent.mkdir(parents=True,exist_ok=True)
 if p.exists():assert p.read_bytes()==raw,('immutable source collision',dest)
 else:p.write_bytes(raw)
 rows.append(dict(path=dest,bytes=len(raw),sha256=hashlib.sha256(raw).hexdigest()))
# Only own workspace is written. Rust will invalidate any stale source-path
# fingerprints. These copied artifacts are rebuildable cache, not proof credit.
cache=[]
raw=json.dumps(cache,sort_keys=True).encode();(b/'NMD_RUST_SEED.json.xz').write_bytes(lzma.compress(raw,preset=6));(b/'NMD_RUST_SEED.json.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\\n')
out=dict(inputs=rows,source_bytes=sum(z['bytes'] for z in rows),cache_files=len(cache),cache_bytes=sum(z['bytes'] for z in cache),cache_manifest_sha256=hashlib.sha256(raw).hexdigest(),free_bytes=shutil.disk_usage(b).free)
(b/'NMD_NATIVE_SEED.json').write_text(json.dumps(out,indent=1));print(json.dumps(out))
''')
assert r.returncode==0,r.stderr
x=json.loads(r.stdout);x['frozen_input_archive']=dict(path=str(archive),bytes=archive.stat().st_size,sha256=hashlib.sha256(archive.read_bytes()).hexdigest());(E/'NMD_NATIVE_SEED.json').write_text(json.dumps(x,indent=1))
r=ssh('python3',f'''from pathlib import Path
import json,base64
b=Path({B!r});print(json.dumps({{n:base64.b64encode((b/n).read_bytes()).decode() for n in ['NMD_RUST_SEED.json.xz','NMD_RUST_SEED.json.sha256']}}))''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():(E/n).write_bytes(base64.b64decode(t))
print(json.dumps({k:x[k] for k in ['source_bytes','cache_files','cache_bytes','free_bytes']}))
