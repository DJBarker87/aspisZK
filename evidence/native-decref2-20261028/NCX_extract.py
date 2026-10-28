from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon')
A=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/aeneas-b59d5188-extended')
S=B/'NCX_ref';(S/'src').mkdir(parents=True,exist_ok=True)
(S/'Cargo.toml').write_text('[package]\nname="ncx_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n')
cast=len(sys.argv)>1 and sys.argv[1]=='NCX_CastRef'
if cast:sys.argv.pop(1)
(S/'src/lib.rs').write_bytes((B/('NCX_cast_reference.rs' if cast else 'NCX_reference.rs')).read_bytes())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
parser=os.environ.get('NCX_EXTRACT_PARSER')=='1'
roots=['crate::'+n for n in sys.argv[1:]] if len(sys.argv)>1 else ['crate::decode_verifier_registry_v2','crate::decode_verifier_registry_entry_v2']
roots+=['crate::option_item']
namespace='NCX_CastRef' if cast else 'NCX_Reference'
dest=B/('NCX_cast_extracted' if cast else 'NCX_extracted')
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--include','core::result::_::unwrap']

for root in roots:cmd+=['--start-from',root]
cmd+=['--dest-file',str(B/'NCX_reference.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']

env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NCX_ref_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',aeneas_origin='b59d5188 extended binary; imported read-only, no tool patches by NCV')
(B/'NCX_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',namespace,'-dest',str(dest),'-subdir',namespace,'-split-files',str(B/'NCX_reference.llbc')]
template=dest/namespace/'FunsExternal_Template.lean'
if template.exists():template.unlink() # own generated output only; exclude stale external templates
print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(aeneas_command=cmd,exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()})
(B/'NCX_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=2))
raise SystemExit(r.returncode)
