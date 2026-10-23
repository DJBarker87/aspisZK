#!/usr/bin/env python3
"""Extract owned SDK iterator reference, retaining full SDK fields and actual Vec operations."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');phase,tag=sys.argv[1:3];P=H/tag
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release');A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(k,None)
assert (P/'src/lib.rs').is_file()
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-'+phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--opaque','crate','--opaque','aspis_s126_owned_sdk','--opaque','core']
 for root in ['crate::source_begin','crate::source_next']:
  cmd+=['--start-from',root,'--include',root]
 for layout in ['crate::DataPointer','crate::SourceIterator','core::option::Option']+['aspis_s126_owned_sdk::'+n for n in ['OwnedSdk','OwnedAccount','OwnedDataCell','OwnedLamportsCell']]:
  cmd+=['--include',layout]
 cmd+=['--dest-file',str(P/'Iterator.llbc'),'--','--manifest-path',str(P/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 x=json.loads((P/'Iterator.llbc').read_text());assert not x['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisS2SdkIterator','-dest',str(P/'generated'),'-subdir','AspisS2SdkIterator','-split-files','-emit-json',str(P/'Iterator.llbc')]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
stdlib=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter/macros.rs')
(P/(phase+'-input.json')).write_text(json.dumps(dict(command=cmd,source_sha256=sha(P/'src/lib.rs'),stdlib_source_sha256=sha(stdlib),tool_pins={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]},qualification='Full owned SDK iterator constructor and next reference. Native operation correspondence is a separate Kani check; no complete stage1 claim.'),indent=2)+'\n')
os.chdir(P)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/(tag+'-'+phase)),'Owned SDK iterator: cached release compilation then focused constructor/next extraction, no full SDK replay','--',*cmd]))
