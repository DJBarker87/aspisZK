"""Direct frozen M31 inverse extraction; same D188 actual-body route as NEI."""
from pathlib import Path
import os,subprocess,json,hashlib,re
B=Path(__file__).resolve().parent;S=B/'NEW_src'
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=C.with_name('aeneas-b59d5188-extended')
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
out=B/'NEW_actual_extracted';out.mkdir(exist_ok=True)
mini=B/'NEW_inverse_extract';(mini/'src').mkdir(parents=True,exist_ok=True)
(mini/'Cargo.toml').write_text('[package]\nname="new_inverse_extract"\nversion="0.1.0"\nedition="2021"\n[workspace]\n[dependencies]\naspis-core={path="../NEW_src/crates/aspis-core",features=["r0"]}\n')
(mini/'src/lib.rs').write_text('use aspis_core::field::M31;\npub fn NEW_inverse(x:M31)->M31{x.inv()}\n')
if not (mini/'Cargo.lock').exists():(mini/'Cargo.lock').write_bytes((S/'Cargo.lock').read_bytes())
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::NEW_inverse','--include','aspis_core::field','--dest-file',str(B/'NEW_InverseActual.llbc'),'--','--manifest-path',str(mini/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEW_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,lock_before=sha(S/'Cargo.lock'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',root='aspis_core::field::M31::inv',field_sha256=sha(S/'crates/aspis-core/src/field.rs'),toolchain='nightly-2026-09-17',feature_scope='core r0; inverse/square_n/mul/reducer body parity checked independently')
(B/'NEW_ACTUAL_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
pins['wrapper_source_sha256']=sha(mini/'src/lib.rs')
r=subprocess.run(cmd,cwd=mini,env=env);pins['charon_exit']=r.returncode
if r.returncode==0:
 pins['llbc_sha256']=sha(B/'NEW_InverseActual.llbc')
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NEW_InverseActual','-dest',str(out),'-subdir','NEW_InverseActual','-split-files',str(B/'NEW_InverseActual.llbc')]
 pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env)
if r.returncode==0:
 text=(out/'NEW_InverseActual/Funs.lean').read_text()
 assert re.search(r'def aspis_core\.field\.M31\.inv\s',text) and re.search(r'def NEW_inverse\s',text),'EMPTY/MISSING extraction root: excluded'
 assert 'FunsExternal' not in text,'External field hole: excluded'
 pins['wrapper_lock_sha256']=sha(mini/'Cargo.lock')
 pins['root_presence_checked']=True
pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in out.rglob('*') if p.is_file()})
(B/'NEW_ACTUAL_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
assert pins['lock_before']==pins['lock_after'],'STOP extraction lock drift'
raise SystemExit(r.returncode)
