"""Read-only capture of exact reached std source and body hashes."""
from pathlib import Path
import subprocess,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownb-20261029'
rels=['alloc/src/vec/in_place_collect.rs','alloc/src/vec/in_place_drop.rs','alloc/src/vec/into_iter.rs','core/src/iter/adapters/filter.rs','core/src/iter/adapters/flatten.rs','alloc/src/vec/spec_from_iter.rs','alloc/src/vec/spec_from_iter_nested.rs']
code='''from pathlib import Path
import json,hashlib
base=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
rows=[]
for rel in RELS:
 p=base/rel;b=p.read_bytes();rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(rows))
'''.replace('RELS',repr(rels))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'deployed-collector-sources.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
