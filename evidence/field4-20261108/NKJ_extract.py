from pathlib import Path
import hashlib,json,subprocess,os
B=Path(__file__).resolve().parent;S=B/'NKJ_src';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
C=B/'NKJ_bin/charon';A=B/'NKJ_bin/aeneas-b59d5188-extended'
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
lock=sha(S/'Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--opaque','crate::field::qm31_from_karatsuba_channel_sums']
for f in ['NKJ_accumulate','NKJ_small2','NKJ_small3','NKJ_small4']:cmd+=['--start-from','crate::field::NKJ_reference::'+f]
cmd+=['--dest-file',str(B/'NKJ_inputs/NKJ_reference.llbc'),'--','--manifest-path',str(S/'crates/aspis-core/Cargo.toml'),'--features','r0','--offline','--locked','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NKJ_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Copt-level=3 -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
r=subprocess.run(cmd,cwd=S,env=env);rc=r.returncode
acmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NKJ_Extracted','-dest',str(B/'NKJ_raw'),'-subdir','NKJ_Extracted','-split-files',str(B/'NKJ_inputs/NKJ_reference.llbc')]
if rc==0:rc=subprocess.run(acmd,cwd=B,env=env).returncode
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,aeneas_command=acmd,charon_exit=r.returncode,exit=rc,lock_before=lock,lock_after=sha(S/'Cargo.lock'),CARGO_TARGET_DIR=env['CARGO_TARGET_DIR'],toolchain=env['RUSTUP_TOOLCHAIN'],outputs={str(p.relative_to(B)):dict(sha256=sha(p),bytes=p.stat().st_size) for base in [B/'NKJ_inputs',B/'NKJ_raw'] for p in base.rglob('*') if p.is_file()})
(B/'NKJ_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2));assert pins['lock_before']==pins['lock_after']
raise SystemExit(rc)
