"""Pinned actual decoder extraction, native source unchanged; no closure credit."""
from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent
C=B.parent/'codex-cx-extraction-repro1-20261027/XRa_bin/charon';A=C.parent/'aeneas-b59d5188-extended'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
S=B/'NFO_ref';D=B/'NFO_decode_extracted';D.mkdir(exist_ok=True)
roots=['aspis_statement::pool_v1::pair_forest_terminal::decode_pool_v1_pair_forest_terminal_result_v1','aspis_statement::pool_v1::pair_forest_terminal::transition_kind','aspis_statement::pool_v1::pair_forest_terminal::validate_result','aspis_statement::pool_v1::pair_terminal::decode_pool_v1_pair_verified_afterstate_v1','aspis_statement::atomic_statement::decode_digest_canonical']
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in roots:cmd+=['--include',root]
cmd+=['--start-from','crate::decode_ref','--dest-file',str(B/'NFO_decode.llbc'),'--','--manifest-path',str(S/'Cargo.toml'),'--offline','--release','--lib','--jobs','1']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NFO_ref_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),rust_reference_sha256=sha(S/'src/lib.rs'),charon_command=cmd,toolchain='nightly-2026-09-17',model_status='new actual-source candidate only; no adopted decoder bridge yet',frozen_lock_before=sha(S/'Cargo.lock'))
(B/'NFO_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode;pins['lock_after']=sha(S/'Cargo.lock')
if not r.returncode:
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NFO_DecodeExtracted','-dest',str(D),'-subdir','NFO_DecodeExtracted','-split-files',str(B/'NFO_decode.llbc')]
 pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env);pins['aeneas_exit']=r.returncode
 pins['outputs']={str(p.relative_to(B)):dict(sha256=sha(p),size=p.stat().st_size) for p in D.rglob('*') if p.is_file()}
(B/'NFO_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1)+'\n');sys.exit(r.returncode)
