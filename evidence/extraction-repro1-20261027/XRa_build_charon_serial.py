from pathlib import Path
import subprocess,os,hashlib,json
B=Path(__file__).resolve().parent
S=B/'XRa_toolchain/charon'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_TARGET_DIR=str(B/'XRa_charon-target'),CARGO_BUILD_JOBS='1',RAYON_NUM_THREADS='1',CARGO_NET_OFFLINE='true')
for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:env.pop(k,None)
env['RUSTFLAGS']='-Zthreads=1 -C link-arg=-Wl,--threads=1'
for cmd in [['/home/dombarker/.cargo/bin/rustc','-vV'],['/home/dombarker/.cargo/bin/cargo','+nightly-2026-06-01','build','--release','--locked','--offline','-j','1','--manifest-path',str(S/'charon/Cargo.toml'),'--bin','charon','--bin','charon-driver']]:
 print('COMMAND',cmd,flush=True);subprocess.run(cmd,cwd=S,env=env,check=True)
rows=[]
for n in ['charon','charon-driver']:
 p=B/'XRa_charon-target/release'/n
 rows.append({'name':n,'sha256':hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),'bytes':p.stat().st_size})
print(json.dumps(rows),flush=True)
(B/'XRa_charon_outputs.json').write_text(json.dumps(rows,indent=2)+'\n')
