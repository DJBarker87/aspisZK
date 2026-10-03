import pathlib,hashlib,json,subprocess
base=pathlib.Path('/home/dombarker/project-offloads/ZK-v5-formal/toolchains/charon')
rust=pathlib.Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/rustc-src/rust/compiler')
files={str(p):rust/p for p in map(pathlib.Path,['rustc_middle/src/mir/mod.rs','rustc_middle/src/mir/basic_blocks.rs','rustc_middle/src/mir/syntax.rs','rustc_middle/src/mir/statement.rs','rustc_middle/src/mir/terminator.rs','rustc_span/src/lib.rs','rustc_middle/src/mir/pretty.rs'])}
files.update({str(p):base/p for p in map(pathlib.Path,['charon/Cargo.toml','charon/Cargo.lock','charon/rust-toolchain','charon/src/bin/charon-driver/translate/get_mir.rs','charon/src/bin/charon-driver/translate/translate_bodies.rs','charon/target/release/charon','charon/target/release/charon-driver','bin/charon'])})
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  while True:
   b=f.read(1048576)
   if not b:break
   h.update(b)
 return h.hexdigest()
print(json.dumps({'classification':'machine-generated primary file hash receipt; source reads only','charon_revision':subprocess.check_output(['git','-C',str(base),'rev-parse','HEAD']).decode().strip(),'rustc_version':subprocess.check_output(['/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/bin/rustc','--version','--verbose']).decode(),'files':{k:{'absolute_path':str(p),'sha256':digest(p),'bytes':p.stat().st_size} for k,p in files.items()}},indent=2))
