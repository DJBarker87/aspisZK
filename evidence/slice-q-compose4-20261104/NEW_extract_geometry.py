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
out=B/'NEW_geometry_extracted';out.mkdir(exist_ok=True)
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--start-from','crate::verifier::NEW_geometry_root','--include','crate::verifier','--include','crate::fast_domain','--include','aspis_core::field','--include','aspis_core::r0::domain','--dest-file',str(B/'NEW_GeometryActual.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEW_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,lock_before=sha(S/'Cargo.lock'),frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',root='verifier::QueryGeometry::for_range',field_sha256=sha(S/'crates/aspis-core/src/field.rs'),toolchain='nightly-2026-09-17',feature_scope='core r0; inverse/square_n/mul/reducer body parity checked independently')
(B/'NEW_GEOMETRY_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
pins['verifier_source_sha256']=sha(S/'crates/aspis-r1-cost-probe/src/verifier.rs')
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
if r.returncode==0:
 pins['llbc_sha256']=sha(B/'NEW_GeometryActual.llbc')
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NEW_GeometryActual','-dest',str(out),'-subdir','NEW_GeometryActual','-split-files',str(B/'NEW_GeometryActual.llbc')]
 pins['aeneas_command']=cmd;r=subprocess.run(cmd,cwd=B,env=env)
if r.returncode==0:
 text=(out/'NEW_GeometryActual/Funs.lean').read_text()
 assert 'verifier.QueryGeometry.for_range' in text and 'verifier.NEW_geometry_root' in text,'EMPTY/MISSING geometry root: excluded'
 pins['external_templates']=[str(p.relative_to(B)) for p in out.rglob('*Template*') if p.is_file()]
 pins['root_presence_checked']=True
pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in out.rglob('*') if p.is_file()})
(B/'NEW_GEOMETRY_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n')
assert pins['lock_before']==pins['lock_after'],'STOP extraction lock drift'
raise SystemExit(r.returncode)
