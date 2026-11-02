"""Read-only provenance check. No compiler, native fixture or capped scope runs."""
from pathlib import Path
import hashlib, json, shlex, subprocess
D=Path(__file__).parent
root='/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/'
items={
 'inputs/io/fs.rs':'std/src/fs.rs',
 'inputs/io/fs-unix.rs':'std/src/sys/fs/unix.rs',
 'inputs/io/fd-unix.rs':'std/src/sys/fd/unix.rs',
 'inputs/io/mod.rs':'std/src/io/mod.rs',
 'inputs/io/small_c_string.rs':'std/src/sys/helpers/small_c_string.rs',
 'inputs/io/pal-unix.rs':'std/src/sys/pal/unix/mod.rs',
 'inputs/io/owned-fd.rs':'std/src/os/fd/owned.rs',
 'inputs/io/c_string.rs':'alloc/src/ffi/c_str.rs',
 'inputs/io/core-fmt.rs':'core/src/fmt/mod.rs',
}
code='import pathlib,hashlib,json; items='+repr(items)+'; root='+repr(root)+'; print(json.dumps({k:dict(path=root+v,sha256=hashlib.sha256(pathlib.Path(root+v).read_bytes()).hexdigest()) for k,v in items.items()}))'
cmd=['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)]
p=subprocess.run(cmd,capture_output=True,text=True)
assert p.returncode==0,p.stderr
remote=json.loads(p.stdout)
for name,r in remote.items():
 r['snapshot_sha256']=hashlib.sha256((D/name).read_bytes()).hexdigest()
 r['equal']=r['snapshot_sha256']==r['sha256']
assert all(r['equal'] for r in remote.values())
result=dict(classification='read-only deployed rust-src snapshot identity, not a formal or native execution result',
 toolchain='1.94.1-x86_64-unknown-linux-gnu',command=cmd,exit=p.returncode,inputs=remote,
 source_capture='The five newly retained helper/owner/CString/Formatter files were copied by scp from these exact paths; the other four snapshots were retained by D571.',
 profile='Adopted client inherits release opt3, debug_assertions=false, overflow_checks=false, panic=abort. This source inspection does not establish a compiled std UB-check setting.',
 memory_scope='N/A read-only source hashing; no Lean/Rust compiler or native gate launched',print_axioms='N/A')
(D/'PV_O11_io-provenance.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(ok=True,matched=len(remote),scopes=0)))
