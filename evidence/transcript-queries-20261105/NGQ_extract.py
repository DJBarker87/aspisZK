"""One pinned extraction of the actual frozen sampler, not a handwritten replacement."""
from pathlib import Path
import json,subprocess,os,sys,hashlib
B=Path(__file__).resolve().parent;x=json.loads((B/sys.argv[1]).read_text());a=x['attempt']
C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.parent/'aeneas-b59d5188-extended';sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
S=B/'NGQ_src';lock=sha(S/'Cargo.lock');assert lock=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
llbc=B/(a+'.llbc');dest=B/'NGQ_extracted'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::r0_transcript::queries_from_pairs','--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-core/Cargo.toml'),'--features','r0','--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NGQ_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),source_sha256=sha(S/'crates/aspis-core/src/r0_transcript.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',namespace='NGQ_SamplerRaw',input_lock=lock)
P=B/(a+'-extraction-pins.json');P.write_text(json.dumps(pins,indent=1));print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
if r.returncode:P.write_text(json.dumps(pins,indent=1));raise SystemExit(r.returncode)
cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NGQ_SamplerRaw','-dest',str(dest),'-subdir','NGQ_SamplerRaw','-split-files',str(llbc)];pins['aeneas_command']=cmd
r=subprocess.run(cmd,cwd=B,env=env);pins.update(exit=r.returncode,outputs={str(p.relative_to(B)):sha(p) for p in dest.rglob('*') if p.is_file()},lock_after=sha(S/'Cargo.lock'));assert pins['lock_after']==lock
P.write_text(json.dumps(pins,indent=1));raise SystemExit(r.returncode)
