"""Capture additional deployed Rust library sources, read-only."""
from pathlib import Path
import subprocess,json
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd4-20261029'
code='''from pathlib import Path
import json,hashlib
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
rows=[]
for n in ['default.rs','slice/iter/macros.rs','iter/adapters/enumerate.rs','ptr/non_null.rs','ptr/mut_ptr.rs']:
 p=root/n;b=p.read_bytes();rows.append(dict(path=str(p),relative=n,sha256=hashlib.sha256(b).hexdigest(),text=b.decode()))
print(json.dumps(rows))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3','-'],input=code,text=True,capture_output=True);assert r.returncode==0,r.stderr
(E/'v237-library-sources.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
print('Five additional1.94.1 default/mutable-iterator/enumerate source files captured read-only.')
