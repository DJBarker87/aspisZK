from pathlib import Path
import subprocess,json,hashlib,os
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'NEF_ref';(S/'src').mkdir(parents=True,exist_ok=True)
(S/'Cargo.toml').write_text('[package]\nname="nef_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n')
reference={'transcript':'NEF_transcript_reference.rs','registry':'NEF_registry_reference.rs'}.get(os.environ.get('NEF_EXTRA'),'NEF_reference.rs')
(S/'src/lib.rs').write_bytes((B/'NEF_reference.rs').read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=['crate::NEF_inv_static']
namespace='NEF_Reference'
if os.environ.get('NEF_EXTRACT_CONFIG'):
 cfg=json.loads(os.environ['NEF_EXTRACT_CONFIG']);roots=cfg['roots'];namespace=cfg['namespace']
dest=B/'NEF_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'NEF_reference.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NEF_ref_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCO')
(B/'NEF_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
pins['llbc_sha256']=sha(B/'NEF_reference.llbc')
pins['llbc_bytes']=(B/'NEF_reference.llbc').stat().st_size
(B/'NEF_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(dest),'-subdir',namespace,'-split-files',str(B/'NEF_reference.llbc')]
print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()})
(B/'NEF_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
