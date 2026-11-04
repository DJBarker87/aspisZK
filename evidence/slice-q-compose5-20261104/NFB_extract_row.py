"""Extract exact local-log G, never the multiplication body."""
from pathlib import Path
import os,subprocess,json,hashlib
B=Path(__file__).resolve().parent;S=B/'NFB_src';M=B/'NFB_row_ref';O=B/'NFB_row_extracted'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.with_name('aeneas-b59d5188-extended')
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';assert sha(S/'Cargo.lock')==frozen
(M/'src').mkdir(parents=True,exist_ok=True);O.mkdir(exist_ok=True)
(M/'src/lib.rs').write_bytes((B/'NFB_row_ref.rs.txt').read_bytes())
(M/'Cargo.toml').write_text('[package]\nname="nfb_row_ref"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-core={path="../NFB_src/crates/aspis-core",features=["r0"]}\n')
assert not (M/'Cargo.lock').exists();(M/'Cargo.lock').write_bytes((S/'Cargo.lock').read_bytes())
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::NFB_row','--include','aspis_core::r0::domain','--include','aspis_core::field','--dest-file',str(B/'NFB_RowRef.llbc'),'--','--manifest-path',str(M/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NFB_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,lock_before=sha(S/'Cargo.lock'),wrapper_lock_before=sha(M/'Cargo.lock'),reference_sha256=sha(M/'src/lib.rs'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',toolchain='nightly-2026-09-17',field_multiplication='not called; local opaque log')
r=subprocess.run(cmd,cwd=M,env=env);pins['charon_exit']=r.returncode
if r.returncode==0:
 pins['llbc_sha256']=sha(B/'NFB_RowRef.llbc')
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NFB_RowRef','-dest',str(O),'-subdir','NFB_RowRef','-split-files',str(B/'NFB_RowRef.llbc')]
 pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env)
if r.returncode==0:
 text=(O/'NFB_RowRef/Funs.lean').read_text();assert 'def NFB_row\n' in text or 'def NFB_row ' in text
 assert 'def aspis_core.field.M31.mul ' not in text,'Unexpected field multiplication in G'
 pins['root_presence_checked']=True
pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),wrapper_lock_after=sha(M/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in O.rglob('*') if p.is_file()})
(B/'NFB_ROW_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');assert pins['lock_after']==frozen
raise SystemExit(r.returncode)
