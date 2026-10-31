from pathlib import Path
import json,hashlib
H=Path('/home/dombarker/project-offloads/codex-pv-b3q2-20261031');R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
files=['core/src/slice/raw.rs','core/src/ptr/metadata.rs','core/src/ptr/const_ptr.rs','core/src/ptr/mut_ptr.rs','core/src/slice/iter.rs','core/src/slice/iter/macros.rs','core/src/ub_checks.rs','core/src/intrinsics/mod.rs','core/src/iter/adapters/enumerate.rs','core/src/iter/range.rs','core/src/iter/adapters/rev.rs']
x=[]
for rel in files:
 p=R/rel;x.append(dict(file=rel,path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),text=p.read_text()))
(H/'pointer-source-capture.json').write_text(json.dumps(dict(toolchain='1.94.1',files=x),indent=2)+'\n')
print(json.dumps(dict(files=len(x),hashes={r['file']:r['sha256']for r in x})))
