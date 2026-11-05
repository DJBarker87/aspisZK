"""One actual-body extraction; frozen source unchanged except a cfg-owned entry."""
from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent;S=B/'NGU_src';C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.with_name('aeneas-b59d5188-extended');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
entry=S/'crates/aspis-r1-cost-probe/src/verifier.rs';old=entry.read_bytes()
entry.write_bytes(old+b'\n#[cfg(NGU_extract)] pub fn NGU_extraction_entry<H:Digest32>(sem:&crate::r1_semantic::Verified<H>,y1:&[u8],inactive:E,g:&[E;29],kappa:E)->Result<E,Error>{prepared_claim(sem,y1,inactive,g,kappa)}\n')
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'

cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::verifier::NGU_extraction_entry']
for mod in ['crate::transcript','crate::weights','crate::r1_semantic','crate::r1_wire','aspis_core::field','aspis_core::circle','crate::fast_pairing','crate::trace']:
 cmd+=['--opaque',mod+'::_']
for ty in ['crate::transcript::Transcript','crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Challenges','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint','crate::fast_pairing::EbyKDot','crate::fast_pairing::canonical::Dot']:
 cmd+=['--include',ty]
cmd+=['--include','crate::verifier::prepared_claim','--dest-file',str(B/'NGU_actual.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NGU_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='--cfg NGU_extract -Copt-level=3 -Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,toolchain='nightly-2026-09-17',lock_before=sha(S/'Cargo.lock'),source_before_sha256=hashlib.sha256(old).hexdigest(),source_with_wrapper_sha256=sha(entry),frozen_body_unchanged=True,scope='prepared_claim actual frozen body; weights/field/Dot/trace callees opaque; raw output UNVALIDATED and not part of the admitted canonical packet')
(B/'NGU_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));print(json.dumps(pins),flush=True)
try:
 r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
 if r.returncode==0:
  pins['llbc_sha256']=sha(B/'NGU_actual.llbc')
  cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NGU_Actual','-dest',str(B/'NGU_extracted'),'-subdir','NGU_Actual','-split-files',str(B/'NGU_actual.llbc')];pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
 pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in (B/'NGU_extracted').rglob('*') if p.is_file()})
 assert pins['lock_before']==pins['lock_after'],'STOP extraction lock drift'
finally:
 entry.write_bytes(old)
 (B/'NGU_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1))
sys.exit(r.returncode)
