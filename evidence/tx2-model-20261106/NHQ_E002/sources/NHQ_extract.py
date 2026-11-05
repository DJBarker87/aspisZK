"""Single extraction of actual prepare; pinned NCO tools, no frozen body edit."""
from pathlib import Path
import subprocess,json,hashlib,os,sys
B=Path(__file__).resolve().parent;S=B/'NHQ_src';C=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin/charon');A=C.with_name('aeneas-b59d5188-extended');sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(C)=='daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8'
assert sha(A)=='c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'
assert sha(S/'Cargo.lock')=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
cmd=[str(C),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or','--start-from','crate::verifier::candidate::tx2_authenticated']
opacity=['crate::r1_semantic::_','crate::r1_wire::_','aspis_core::field::_','aspis_core::circle::_',
 'crate::verifier::candidate::parse_shape','crate::verifier::candidate::resume',
 'crate::weights::_','crate::verifier::candidate::batch_merkle','crate::verifier::candidate::query_loop',
 'crate::verifier::finish_relation','crate::verifier::_']
for name in opacity: cmd+=['--opaque',name]
cmd+=['--include','crate::verifier::candidate::tx2_authenticated','--include','crate::verifier::candidate::tx2_common']
for ty in ['crate::verifier::Prepared','crate::verifier::Accumulator','crate::verifier::BatchedWeights','crate::verifier::View','crate::verifier::Error','crate::verifier::Variant','crate::verifier::Phase','crate::verifier::QueryGeometry','crate::r1_semantic::Verified','crate::r1_wire::SemanticTranscript','crate::r1_wire::Challenges','aspis_core::field::M31','aspis_core::field::CM31','aspis_core::field::QM31','aspis_core::field::wide_exact::WideExact','aspis_core::circle::SecureCirclePoint']:
 cmd+=['--include',ty]
cmd+=['--dest-file',str(B/'NHQ_actual.llbc'),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_TARGET_DIR=str(B/'NHQ_extract_target'),CARGO_NET_OFFLINE='true',CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
pins=dict(opacity=opacity,charon_sha256=sha(C),aeneas_sha256=sha(A),charon_command=cmd,toolchain='nightly-2026-09-17',lock_before=sha(S/'Cargo.lock'),actual_candidate_sha256=sha(S/'crates/aspis-r1-cost-probe/src/candidate.rs'),frozen_body_unchanged=True)
(B/'NHQ_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));print(json.dumps(pins),flush=True)
r=subprocess.run(cmd,cwd=S,env=env);pins['charon_exit']=r.returncode
if r.returncode==0:
 pins['llbc_sha256']=sha(B/'NHQ_actual.llbc')
 cmd=[str(A),'-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NHQ_Actual','-dest',str(B/'NHQ_extracted'),'-subdir','NHQ_Actual','-split-files',str(B/'NHQ_actual.llbc')];pins['aeneas_command']=cmd;print(json.dumps(cmd),flush=True);r=subprocess.run(cmd,cwd=B,env=env)
pins.update(exit=r.returncode,lock_after=sha(S/'Cargo.lock'),outputs={str(p.relative_to(B)):sha(p) for p in (B/'NHQ_extracted').rglob('*') if p.is_file()})
(B/'NHQ_EXTRACTION_PINS.json').write_text(json.dumps(pins,indent=1));assert pins['lock_before']==pins['lock_after'],'STOP extraction lock drift'
sys.exit(r.returncode)
