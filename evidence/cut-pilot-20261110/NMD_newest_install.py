"""Install only the release-required Rust in this job's private rustup home."""
from pathlib import Path
import os,subprocess,json,hashlib
B=Path.cwd();K=B/'NMD_newest/kani-0.68.0';version=(K/'rust-toolchain-version').read_text().strip()
env=dict(os.environ,RUSTUP_HOME=str(B/'NMD_rustup'),CARGO_HOME=str(B/'NMD_newest_cargo'))
cmd=['/home/dombarker/.cargo/bin/rustup','toolchain','install',version,'--profile','minimal','--component','rustc-dev,rust-src,llvm-tools-preview','--no-self-update']
r=subprocess.run(cmd,env=env)
x=dict(command=cmd,exit=r.returncode,toolchain=version,private_rustup=env['RUSTUP_HOME'],binary_sha256={str(p.relative_to(B)):hashlib.sha256(p.read_bytes()).hexdigest() for p in (K/'bin').iterdir() if p.is_file()})
(B/'NMD_NEWEST_INSTALL.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x));raise SystemExit(r.returncode)
