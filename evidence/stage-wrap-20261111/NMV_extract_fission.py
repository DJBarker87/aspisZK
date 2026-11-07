from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
T=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')
C=T/'charon'; A=T/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
S=B/'NMV_fission_ref';(S/'src').mkdir(parents=True,exist_ok=True)
(S/'Cargo.toml').write_text('[package]\nname="nmv_fission"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[features]\ncu-profiling=[]\n')
(S/'src/lib.rs').write_bytes((B/'NMV_Fission.rs').read_bytes())
# Dependency-free fission copy, no release crate is rebuilt or altered.
(S/'Cargo.lock').write_text('version = 4\n\n[[package]]\nname = "nmv_fission"\nversion = "0.1.0"\n')
llbc=B/'NMV_fission.llbc';dest=B/'NMV_fission_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--start-from','crate::stage1','--start-from','crate::stage2','--dest-file',str(llbc),'--','--manifest-path',str(S/'Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NMV_fission_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_source_sha256=sha(S/'src/lib.rs'),manifest_sha256=sha(S/'Cargo.toml'),lock_before=sha(S/'Cargo.lock'),charon_command=cmd,toolchain='nightly-2026-09-17',features=[],ruling='bn',dependency_free=True)
(B/'NMV_FISSION_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
try:
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
 if r.returncode==0:
  doc=json.loads(llbc.read_text());assert not doc['has_errors']
  pins['llbc_sha256']=sha(llbc)
  cmd=[str(A),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NMV_Fission','-dest',str(dest),'-subdir','NMV_Fission','-split-files',str(llbc)]
  pins['aeneas_command']=cmd
  r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
 pins['exit']=r.returncode
finally:
 pins['lock_after']=sha(S/'Cargo.lock');assert pins['lock_after']==pins['lock_before']
 pins['outputs']={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()}
 (B/'NMV_FISSION_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
