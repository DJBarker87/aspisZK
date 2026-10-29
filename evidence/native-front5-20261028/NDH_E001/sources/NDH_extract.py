from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'NDH_ref';(S/'src').mkdir(parents=True,exist_ok=True)
(S/'Cargo.toml').write_text('[package]\nname="ndh_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n')
(S/'src/lib.rs').write_bytes((B/'NDH_src/crates/aspis-r1-cost-probe/src/NDH_reference.rs').read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::table_ref','crate::fibre_get_ref','crate::fibre_valid_ref','crate::slot_ref','crate::flag_ref','crate::retirement_ref','crate::status_ref','crate::admitted_ref']
namespace='NDH_Reference'
dest=B/'NDH_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'NDH_reference.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NDH_ref_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'NDH_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(dest),'-subdir',namespace,'-split-files',str(B/'NDH_reference.llbc')]
print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()})
(B/'NDH_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
