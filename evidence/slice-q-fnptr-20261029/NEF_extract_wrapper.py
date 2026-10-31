from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent;S=B/'NEF_src';C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
lock=sha(S/'Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
assert sha(S/'crates/aspis-core/src/field.rs')=='28df5a1abee13bde4b3aa9eeceb0489bedf00531f298460954a97661f5f1baea'
roots=['crate::field::_::inv','crate::field::_::inv_with']
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'NEF_wrapper.llbc'),'--','--manifest-path',str(S/'crates/aspis-core/Cargo.toml'),'--locked','--offline','--release','--features','r0','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEF_frozen_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),field_source_sha256=sha(S/'crates/aspis-core/src/field.rs'),lock_sha256=lock,charon_command=cmd,toolchain='nightly-2026-09-17',source='ACTUAL FROZEN field.rs; no arithmetic replacement')
print(json.dumps(pins),flush=True);r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
pins['llbc_sha256']=sha(B/'NEF_wrapper.llbc')
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NEF_FrozenWrapper','-dest',str(B/'NEF_extracted'),'-subdir','NEF_FrozenWrapper','-split-files',str(B/'NEF_wrapper.llbc')]
r=subprocess.run(cmd,cwd=B,env=env);pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in (B/'NEF_extracted/NEF_FrozenWrapper').rglob('*') if p.is_file()},lock_after_sha256=sha(S/'Cargo.lock'));assert pins['lock_after_sha256']==lock
assert any('def ' in p.read_text() for p in (B/'NEF_extracted/NEF_FrozenWrapper').glob('Funs.lean')), 'EMPTY root match gives no extraction credit'
(B/'NEF_WRAPPER_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2)+'\n');print(json.dumps(pins),flush=True);raise SystemExit(r.returncode)
