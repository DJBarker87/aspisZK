"""Pinned NCO extraction of safe caller references; not a closure claim."""
from pathlib import Path
import json,subprocess,os,sys,hashlib
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt'];target=x['module']
roots={'NGM_FinishRef':'crate::finish_ref','NGM_DoubleRef':'crate::double_observed_ref','NGM_HelperRef':'crate::all_refs'};assert target in roots
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.parent/'aeneas-b59d5188-extended';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
S=B/'NGM_ref';(S/'src').mkdir(parents=True,exist_ok=True);(S/'Cargo.toml').write_text('[package]\nname="nfu_reference"\nversion="0.1.0"\nedition="2021"\n[workspace]\n');(S/'src/lib.rs').write_bytes((B/'NGM_references.rs').read_bytes())
llbc=B/(a+'.llbc');dest=B/'NGM_extracted'/target
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from',roots[target],'--dest-file',str(llbc),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NGM_ref_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',namespace=target,claim='REFERENCE EXTRACTION ONLY; caller native/model substitution still OPEN')
P=B/(a+'-extraction-pins.json');P.write_text(json.dumps(pins,indent=1));print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env)
if r.returncode:raise SystemExit(r.returncode)
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace',target,'-dest',str(dest),'-subdir',target,'-split-files',str(llbc)];pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True)
r=subprocess.run(cmd,cwd=B,env=env);pins.update(exit=r.returncode,outputs={str(p.relative_to(B)):sha(p)for p in dest.rglob('*')if p.is_file()});P.write_text(json.dumps(pins,indent=1));raise SystemExit(r.returncode)
