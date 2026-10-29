from pathlib import Path
import json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-diag12-20261029')
S=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/std/src')
files=['fs.rs','io/stdio.rs','io/buffered/linewriter.rs','io/buffered/linewritershim.rs','io/buffered/bufwriter.rs','sys/fs/unix.rs','sys/fd/unix.rs','sys/stdio/unix.rs','sys/pal/unix/mod.rs','sys/fs/mod.rs','sys/stdio/mod.rs','sys/io/mod.rs','os/fd/owned.rs','sys/sync/reentrant_lock.rs']
rows=[]
for f in files:
 p=S/f
 if not p.exists():continue
 dst=D/('source-'+f.replace('/','_')+'.txt');dst.write_bytes(p.read_bytes());rows.append(dict(path=str(p),snapshot=dst.name,sha256=hashlib.sha256(p.read_bytes()).hexdigest()))
(D/'rust-src-pins.json').write_text(json.dumps(rows,indent=2)+'\n')
ext=json.loads((D.parent/'codex-pv-diag5-20261029/external-authority.json').read_text())
for r in ext:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['object_sha256']
for r in json.loads((D/'reuse.json').read_text())['rows']:
 assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
 assert hashlib.sha256(Path(r['source']).read_bytes()).hexdigest()==r['source_sha256']
(D/'external-preflight.json').write_text(json.dumps(dict(external=len(ext),reused=2161,mismatches=[],timing='before first Lean attempt'))+'\n')
print('snapshots',len(rows),'external checked',len(ext))
