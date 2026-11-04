"""One pinned small-function extraction, not the failed production spine."""
from pathlib import Path
import subprocess,json,hashlib,os,sys,tomllib
B=Path(__file__).resolve().parent
C=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon';A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
S=B/'NFV_ref';D=B/'NFV_extracted';D.mkdir(exist_ok=True)
lock=B/'NFV_src/Cargo.lock';frozen_hash=sha(lock);assert frozen_hash=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::result::Result','--start-from','crate::encode_ref','--dest-file',str(B/'NFV_request.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NFV_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',expected_time='optimized dependency compilation, then one small request-encoder MIR/Aeneas translation; no process/HRTB body and no arithmetic aggregation',source_lock_before=frozen_hash,reference_lock_before=sha(S/'Cargo.lock'))
(B/'NFV_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode;pins['source_lock_after']=sha(lock);pins['reference_lock_after']=sha(S/'Cargo.lock')
assert sha(lock)==frozen_hash,'STOP frozen source lock drift'
frozen=tomllib.loads(lock.read_text());resolved=tomllib.loads((S/'Cargo.lock').read_text());key=lambda p:(p['name'],p['version'],p.get('source'))
known={key(p) for p in frozen['package']};added=[key(p) for p in resolved['package'] if key(p) not in known]
pins['reference_added_packages']=added;assert added==[('nfv_request_reference','0.1.0',None)],('STOP dependency drift',added)
if not r.returncode:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NFV_RequestActual','-dest',str(D),'-subdir','NFV_RequestActual','-split-files',str(B/'NFV_request.llbc')]
 pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
 pins['outputs']={str(p.relative_to(B)):dict(sha256=sha(p),size=p.stat().st_size) for p in D.rglob('*') if p.is_file()}
(B/'NFV_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');sys.exit(r.returncode)
