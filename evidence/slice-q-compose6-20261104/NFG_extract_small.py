from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent;S=B/'NFG_src';W=B/'NFG_small_ref';C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=sha(S/'Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
(W/'src').mkdir(parents=True,exist_ok=True)
(W/'Cargo.toml').write_text('[package]\nname="nfg-small-refs"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-core={path="../NFG_src/crates/aspis-core",features=["r0"]}\n')
(W/'src/lib.rs').write_text((S/'NFG_small_refs.rs').read_text())
(W/'Cargo.lock').write_bytes((S/'Cargo.lock').read_bytes())
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NFG_small_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',CARGO_PROFILE_RELEASE_OVERFLOW_CHECKS='true',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::NFG_cm_ref','--start-from','crate::NFG_qm_zero_ref','--dest-file',str(B/'NFG_small.llbc'),'--','--manifest-path',str(W/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),reference_sha256=sha(W/'src/lib.rs'),frozen_lock_sha256=lock,charon_command=cmd,toolchain='nightly-2026-09-17',overflow_checks=True,source='safe Rust references used byte-identically by the actual-function contract harness; wrapper lock is separate from frozen native tree')
print(json.dumps(pins),flush=True);r=subprocess.run(cmd,cwd=W,env=env)
assert sha(S/'Cargo.lock')==lock
if r.returncode:raise SystemExit(r.returncode)
pins['llbc_sha256']=sha(B/'NFG_small.llbc');pins['wrapper_resolved_lock_sha256']=sha(W/'Cargo.lock')
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NFG_SmallRefs','-dest',str(B/'NFG_row_extracted'),'-subdir','NFG_SmallRefs','-split-files',str(B/'NFG_small.llbc')]
r=subprocess.run(cmd,cwd=B,env=env);pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in (B/'NFG_row_extracted/NFG_SmallRefs').rglob('*') if p.is_file()})
assert any('def ' in p.read_text() for p in (B/'NFG_row_extracted/NFG_SmallRefs').glob('Funs.lean'))
(B/'NFG_SMALL_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(pins));raise SystemExit(r.returncode)
