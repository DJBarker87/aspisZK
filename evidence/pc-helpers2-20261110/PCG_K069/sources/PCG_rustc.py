#!/usr/bin/python3
"""Own package-specific deployed SDK cfg selection; no shared tool changes."""
import os,sys,json,subprocess
from pathlib import Path
args=sys.argv[2:]+['-L','dependency=/home/dombarker/project-offloads/codex-pc-helpers2-20261110/PCG_sdk_syscall']
if '--crate-name' in args and args[args.index('--crate-name')+1]=='solana_pubkey':
 root=Path('/home/dombarker/project-offloads/codex-pc-helpers2-20261110')
 out=root/'PCG_sdk_syscall';out.mkdir(exist_ok=True)
 src='/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/solana-define-syscall-2.3.0/src/lib.rs'
 # This is the frozen target-specific edge, absent from Cargo's host selection.
 common=args[args.index('--sysroot'):]
 cmd=[sys.argv[1],'--crate-name','solana_define_syscall','--edition=2021',src,'--crate-type','lib','--emit=dep-info,metadata,link','-C','opt-level=3','-C','overflow-checks=on','--out-dir',str(out),'--target','x86_64-unknown-linux-gnu',*common]
 # Kani compiler options require the same instrumentation flags as the parent.
 cmd+=['-Z','unstable-options','-Z','always-encode-mir','--cfg=kani','-Z','crate-attr=feature(register_tool)','-Z','crate-attr=register_tool(kanitool)']
 if not (out/'PCG_success').exists():
  subprocess.run(cmd,check=True);(out/'PCG_success').write_text('exit0')
 args+=['--cfg','target_os="solana"','-Aexplicit_builtin_cfgs_in_flags','--extern','solana_define_syscall='+str(out/'libsolana_define_syscall.rmeta'),'-L','dependency='+str(out)]
with open('/home/dombarker/project-offloads/codex-pc-helpers2-20261110/PCG_rustc_commands.jsonl','a') as f:f.write(json.dumps([sys.argv[1],*args])+'\n')
os.execv(sys.argv[1],[sys.argv[1],*args])
