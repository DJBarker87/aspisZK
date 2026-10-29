from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdb2f-20261029');out=D/'source';out.mkdir(exist_ok=True)
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src')
paths=[root/p for p in ['ops/try_trait.rs','ops/function.rs','iter/adapters/zip.rs','ptr/non_null.rs','ptr/mut_ptr.rs','ptr/const_ptr.rs','mem/maybe_uninit.rs','slice/mod.rs']]
paths.append(Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/generic-array-0.14.7/src/lib.rs'))
rows=[]
for p in paths:
 raw=p.read_bytes();n=p.name if p.name!='lib.rs'else'generic-array.rs';q=out/n;q.write_bytes(raw);rows.append(dict(path=str(p),snapshot='source/'+n,sha256=hashlib.sha256(raw).hexdigest()))
(D/'extra-source-pins.json').write_text(json.dumps(rows,indent=2));print('Pinned',len(rows),'deployed native source files')
