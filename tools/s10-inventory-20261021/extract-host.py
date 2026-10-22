#!/usr/bin/env python3
"""Pinned, capped full-entrypoint extraction probe. Never edits frozen sources."""
import hashlib,json,os,subprocess,time
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
KIT=Path('/home/dombarker/project-offloads/codex-cx-asq8-kani-20261021/harness')
CHARON=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release/charon')
assert hashlib.sha256(CHARON.read_bytes()).hexdigest()=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
# Time is expected in native optimized dependency compilation, then monomorphized
# entrypoint graph extraction. No elimination, proof generation or SBF rebuild.
for name,manifest,root,features in [
 ('verifier-mono-v2','programs/r1-cost-probe/Cargo.toml','crate::entrypoint','pool-adapter,private-leaf-salts'),
 ('pool-mono-v2','programs/aspis-pool/Cargo.toml','crate::processor::entrypoint','r1-split-checkpoint,pair-forest-source-invariant-audit,pair-forest-source-result-invariant-audit')]:
 out=H/name;out.mkdir(exist_ok=False)
 subprocess.run(['python3',str(KIT/'reservation.py'),str(out/'reservation.json')],check=True)
 cmd=[str(CHARON),'cargo','--mir','elaborated','--sysroot','default','--monomorphize','--extract-opaque-bodies','--start-from',root,'--dest-file',str(out/'Program.llbc'),'--','--manifest-path',str(H/'src'/manifest),'--locked','--offline','--release','--lib','--features',features,'--jobs','1']
 (out/'command.json').write_text(json.dumps(dict(argv=cmd,scope='native diagnostic; target_os=solana and deployed SBF are NOT established',expected_time='optimized dependency compilation followed by monomorphized LLBC extraction',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64)),indent=2)+'\n')
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=str(H/'charon-target'),RUSTFLAGS='-C link-arg=-Wl,--threads=4')
 run=['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(KIT/'capped.py'),str(out/'receipt'),'optimized compilation then entrypoint monomorphized Charon extraction','--',*cmd]
 with (out/'launch.log').open('w') as f:
  p=subprocess.run(run,cwd=H/'src',env=env,stdout=f,stderr=subprocess.STDOUT)
 print(name,p.returncode,flush=True)
