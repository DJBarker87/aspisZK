from pathlib import Path
import os,subprocess,json,hashlib
B=Path(__file__).resolve().parent;C=B/'XRh_new_charon/charon'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',RAYON_NUM_THREADS='1',RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'XRh_charon_target'),RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
cmds=[['rustup','toolchain','install','nightly-2026-09-17','--profile','minimal','--component','rustc-dev,rust-src,llvm-tools'],['cargo','build','--release','--locked','--no-default-features','--features','rustc','-j1','--bin','charon','--bin','charon-driver']]
for cmd in cmds:
 print('COMMAND',cmd,flush=True);subprocess.run(cmd,cwd=C,env=env,check=True)
rows=[]
for n in ['charon','charon-driver']:
 p=B/'XRh_charon_target/release'/n;rows.append(dict(path=str(p),sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),bytes=p.stat().st_size))
(B/'XRh_new_charon_binary.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows),flush=True)
