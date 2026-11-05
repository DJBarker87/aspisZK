"""One actual-body extraction; frozen source unchanged except a cfg-owned entry."""
from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent;S=B/'NGT_src';C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.with_name('aeneas-b59d5188-extended');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
entry=S/'crates/aspis-r1-cost-probe/src/lib.rs';old=entry.read_bytes()
entry.write_bytes(old+b'\n#[cfg(NGT_extract)] pub fn NGT_scalar_entry<H: aspis_core::Digest32>(t:&mut transcript::Transcript<H>,row:u8,payload:&[u8],nonzero:bool)->aspis_core::field::WideExact{t.scalar(row,payload,nonzero)}\n#[cfg(NGT_extract)] pub fn NGT_scalar_k_entry<H: aspis_core::Digest32>(t:&mut transcript::Transcript<H>,row:u8,payload:&[u8])->aspis_core::field::QM31{t.scalar_k(row,payload)}\n')
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::NGT_scalar_entry','--start-from','crate::NGT_scalar_k_entry']
for mod in ['crate::sampler','aspis_core::field','crate::trace']:
 cmd+=['--opaque',mod+'::_']
for ty in ['crate::transcript::Transcript','crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Challenges','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint']:
 cmd+=['--include',ty]
cmd+=['--dest-file',str(B/'NGT_actual.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NGT_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='--cfg NGT_extract -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,toolchain='nightly-2026-09-17',lock_before=sha(S/'Cargo.lock'),source_before_sha256=hashlib.sha256(old).hexdigest(),source_with_wrapper_sha256=sha(entry),frozen_body_unchanged=True)
(B/'NGT_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));print(json.dumps(pins),flush=True)
try:
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
 if r.returncode==0:
  pins['llbc_sha256']=sha(B/'NGT_actual.llbc')
  cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NGT_Actual','-dest',str(B/'NGT_extracted'),'-subdir','NGT_Actual','-split-files',str(B/'NGT_actual.llbc')];pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
 pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in (B/'NGT_extracted').rglob('*') if p.is_file()})
 assert pins['lock_before']==pins['lock_after'],'STOP extraction lock drift'
finally:
 entry.write_bytes(old)
 (B/'NGT_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1))
sys.exit(r.returncode)
