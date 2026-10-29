"""Read-only exact source capture for the remaining collector store/glue cone."""
from pathlib import Path
import json,subprocess,hashlib
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-ownc-20261029'
rels=['alloc/src/vec/mod.rs','alloc/src/vec/spec_extend.rs','alloc/src/vec/set_len_on_drop.rs','alloc/src/raw_vec/mod.rs','core/src/array/iter.rs','core/src/slice/sort/unstable/mod.rs','core/src/slice/sort/shared/smallsort.rs']
code='''from pathlib import Path
import hashlib,json
B=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
rows=[]
for rel in RELS:
 p=B/rel;b=p.read_bytes();rows.append(dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(rows))
'''.replace('RELS',repr(rels))
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
j=dict(scope='deployed 1.94.1 source capture; no completeness or theorem claim',rows=json.loads(r.stdout),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip())
(E/'deployed-tail-sources.json').write_text(json.dumps(j,indent=2)+'\n')
print('captured',len(j['rows']),'files')
