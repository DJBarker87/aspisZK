#!/usr/bin/env python3
"""Extract the reached standard-library any body, not a replacement loop."""
from pathlib import Path
import os,sys,subprocess,json,hashlib
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');phase,tag=sys.argv[1:3];P=H/tag
T=Path('/home/dombarker/project-offloads/aspis-r1-r18-tools-20261016/charon-target/release');A=Path('/home/dombarker/project-offloads/v7-tag73-challenge-qm31-source-20260825-work/toolchain/output/aeneas-b59d5188-lean432-extended-static')
os.environ.update(PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',RUSTUP_TOOLCHAIN='nightly-2026-06-01',CARGO_BUILD_JOBS='1',CARGO_TARGET_DIR=str(H/'owned-charon-target'),CARGO_NET_OFFLINE='true',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-C link-arg=-Wl,--threads=1')
for k in ['RUSTC_WRAPPER','RUSTC_WORKSPACE_WRAPPER','CARGO_ENCODED_RUSTFLAGS','CHARON_TOOLCHAIN_IS_IN_PATH']:os.environ.pop(k,None)
P.mkdir(exist_ok=True);(P/'src').mkdir(exist_ok=True)
(P/'src/lib.rs').write_text('pub fn checkpoint_nonzero(bytes: &[u8]) -> bool { bytes.iter().any(|byte| *byte != 0) }\n')
(P/'Cargo.toml').write_text('[package]\nname="aspis-s126-std-any"\nversion="0.0.0"\nedition="2021"\n[workspace]\n[profile.release]\noverflow-checks=true\n')
subprocess.run(['python3',str(H/'kit/reservation.py'),str(H/(tag+'-'+phase+'-admission.json'))],check=True,stdout=subprocess.DEVNULL)
if phase=='charon':
 cmd=[str(T/'charon'),'cargo','--preset','aeneas','--mir','built','--start-from','crate::checkpoint_nonzero','--include','crate','--opaque','core','--include','core::slice::iter::_::any','--include','core::slice::iter::Iter','--include','core::option::Option','--include','core::result::Result','--include','core::marker::PhantomData','--extract-opaque-bodies','--dest-file',str(P/'StdAny.llbc'),'--','--manifest-path',str(P/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
else:
 x=json.loads((P/'StdAny.llbc').read_text());assert not x['has_errors']
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','AspisS2StdAny','-dest',str(P/'generated'),'-subdir','AspisS2StdAny','-split-files','-emit-json',str(P/'StdAny.llbc')]
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
stdlib=Path('/home/dombarker/.rustup/toolchains/nightly-2026-06-01-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library/core/src/slice/iter/macros.rs')
(P/(phase+'-input.json')).write_text(json.dumps(dict(command=cmd,source_sha256=sha(P/'src/lib.rs'),stdlib_source_sha256=sha(stdlib),tool_pins={str(p):sha(p) for p in [T/'charon',T/'charon-driver',A]},qualification='Concrete reached standard-library body extraction preflight; no source correspondence or SDK closure claimed until bodies and generated output are inspected.'),indent=2)+'\n')
os.chdir(P)
raise SystemExit(subprocess.call(['systemd-run','--user','--scope','-q','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',str(H/'kit/capped.py'),str(H/'receipts'/(tag+'-'+phase)),'Concrete std any: tiny cached release compilation then focused translation, no full SDK replay','--',*cmd]))
