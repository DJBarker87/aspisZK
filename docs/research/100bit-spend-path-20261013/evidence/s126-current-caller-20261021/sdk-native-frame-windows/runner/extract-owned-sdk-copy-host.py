#!/usr/bin/env python3
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');phase,tag=sys.argv[1:3];P=H/tag
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release')
A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(k,None)
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-'+phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
roots=['crate::copy_step','crate::copy_in_place']
layouts=['aspis_s126_owned_sdk::'+n for n in ['OwnedSdk','OwnedAccount','OwnedDataCell','OwnedLamportsCell']]+['solana_program_error::ProgramError','core::result::Result','core::option::Option']
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default']
 for n in ['crate','aspis_s126_owned_sdk','solana_program_error']:cmd+=['--opaque',n]
 for n in roots:cmd+=['--start-from',n,'--include',n]
 for n in layouts:cmd+=['--include',n]
 cmd+=['--dest-file',str(P/'Copy.llbc'),'--','--manifest-path',str(P/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 assert not json.loads((P/'Copy.llbc').read_text())['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisS2SdkCopyReference','-dest',str(P/'generated'),'-subdir','AspisS2SdkCopyReference','-split-files','-emit-json',str(P/'Copy.llbc')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
(P/(phase+'-input.json')).write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',command=cmd,roots=roots,layouts=layouts,source_sha256=sha(P/'src/lib.rs'),owned_sdk_dependency_sha256=sha(H/'owned-sdk-v3/src/lib.rs'),tool_pins={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]}),indent=2)+'\n')
os.chdir(P)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/(tag+'-'+phase)),'Cached optimized compilation and full owned SDK byte-step/count extraction; no arithmetic evaluation','--',*cmd]))
