#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess
H=Path(__file__).resolve().parent
old=H.parent/'codex-cx-s2e-20261023'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
T=H/'heap-target'
subprocess.run(['cp','-a','--reflink=auto',str(H/'sbf-target-verifier'),str(T)],check=True)
for mode,base in [('old',old/'sbf-src'),('new',H/'src')]:
 src=H/('heap-src-'+mode);subprocess.run(['cp','-a','--reflink=auto',str(base),str(src)],check=True)
 lib=src/'programs/r1-cost-probe/src/lib.rs';before=lib.read_text()
 anchor='return r1_pool_adapter::process(program_id,accounts,data);'
 replacement='''let result = r1_pool_adapter::process(program_id,accounts,data);
        #[cfg(target_os="solana")]
        unsafe {
            let start=solana_program::entrypoint::HEAP_START_ADDRESS as usize;
            let cursor=*(start as *const usize);
            let used=start+256*1024-cursor+core::mem::size_of::<usize>();
            solana_program::log::sol_log_64(0xada, used as u64, 256*1024, 0, 0);
        }
        return result;'''
 assert before.count(anchor)==1
 lib.write_text(before.replace(anchor,replacement))
 for p in src.rglob('*.rs'):os.utime(p,None)
 env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_TARGET_DIR=str(T),CARGO_NET_OFFLINE='true',CARGO_TARGET_SBPF_SOLANA_SOLANA_RUSTFLAGS='-C link-arg=--threads=4')
 for k in ['RUSTFLAGS','RUSTC_WRAPPER','RUSTUP_TOOLCHAIN','ASPIS_R1_POOL_PROGRAM_ID','ASPIS_R1_REGISTRY_PROGRAM_ID']:env.pop(k,None)
 cmd=['/home/dombarker/.local/share/solana/install/releases/3.1.13/solana-release/bin/cargo-build-sbf','--manifest-path',str(src/'programs/r1-cost-probe/Cargo.toml'),'--sbf-out-dir',str(H/('heap-artifacts-'+mode)),'--features','pool-adapter,private-leaf-salts','--skip-tools-install','--offline','-j','4','--','--locked']
 subprocess.run(cmd,cwd=src,env=env,check=True)
 elf=H/('heap-artifacts-'+mode)/'aspis_r1_cost_probe_program.so'
 (H/('heap-'+mode+'-pin.json')).write_text(json.dumps({'mode':mode,'sha256':sha(elf),'bytes':elf.stat().st_size,'diagnostic_only':True,'lib_before_sha256':hashlib.sha256(before.encode()).hexdigest(),'lib_after_sha256':sha(lib),'change':replacement,'command':cmd},indent=2)+'\n')
