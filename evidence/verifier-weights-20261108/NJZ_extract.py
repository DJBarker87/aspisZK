"""Own extraction selection; pinned shared tools and frozen staging untouched."""
from pathlib import Path
import json,hashlib,subprocess,os,sys
B=Path(__file__).resolve().parent;S=B/'NJZ_src';O=B/'NJZ_extraction';O.mkdir(exist_ok=True)
P=Path('/home/dombarker/project-offloads/codex-cx-extraction-repro1-20261027/XRa_bin')
pins={'charon':'daad69bea1114042a2d2fbd3dfde99922b152d4f57023bf8edb83e5a6f336af8','aeneas-b59d5188-extended':'c0cf4fccb0879db4ce342da991f6215732a19fc01345b9eec84e632f4673b958'}
for n,h in pins.items():assert hashlib.sha256((P/n).read_bytes()).hexdigest()==h
for n,t in json.loads((B/'NJZ_FROZEN_INPUTS.json').read_text()).items():(S/n).write_text(t)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';assert sha(S/'Cargo.lock')==frozen
roots=['crate::verifier::echeck','crate::verifier::_::raw','crate::verifier::_::e','crate::verifier::_::k','crate::verifier::_::new','crate::verifier::_::value','crate::verifier::_::finish','crate::verifier::read_checkpoint_weights','crate::verifier::read_checkpoint_semantic_alpha','crate::verifier::validate_checkpoint_queries','aspis_statement::pool_v1::format::pool_v1_tree_parent','aspis_statement::pool_v1::incremental_merkle::pool_v1_empty_roots','aspis_statement::pool_v1::incremental_merkle::_::empty','aspis_statement::pool_v1::incremental_merkle::_::default']
cmd=[str(P/'charon'),'cargo','--preset','aeneas','--mir','built','--sysroot','default','--include','core::option::Option','--include','core::result::Result','--include','core::option::_::ok_or']
for root in roots:cmd+=['--start-from',root]
for root in roots[-4:]:cmd+=['--include',root]
# Existing CLOSED field parsers/reduction/heap and compression are child boundaries.
opaque=['aspis_core::field::_::from_le_bytes','aspis_core::field::wide_exact::_::from_le_bytes','aspis_core::field::_::reduce_u64','aspis_core::r0::heap::filled','aspis_statement::poseidon2::merkle_node_compress_v3']
for root in opaque:cmd+=['--opaque',root]
llbc=O/'NJZ.llbc';cmd+=['--dest-file',str(llbc),'--','--manifest-path',str(S/'crates/aspis-r1-cost-probe/Cargo.toml'),'--locked','--offline','--release','--lib','--jobs','1','--features','private-leaf-salts,optimized-terminal,program-build']
aeneas=[str(P/'aeneas-b59d5188-extended'),'-diagnose-translation','-sequential','-no-progress-bar','-abort-on-error','-backend','lean','-namespace','NJZ_Emission','-dest',str(O/'raw'),'-subdir','NJZ_Emission','-split-files',str(llbc)]
env=dict(os.environ,RUSTUP_TOOLCHAIN='nightly-2026-09-17',CARGO_NET_OFFLINE='true',CARGO_TARGET_DIR=str(B/'NJZ_target'),CARGO_BUILD_JOBS='1',RUSTFLAGS='-Zthreads=1 -C link-arg=-Wl,--threads=1',RAYON_NUM_THREADS='1')
record=dict(tools=pins,roots=roots,opaque=opaque,charon_command=cmd,aeneas_command=aeneas,lock_before=sha(S/'Cargo.lock'))
try:
 r=subprocess.run(cmd,cwd=S,env=env);record['charon_exit']=r.returncode
 if r.returncode==0:
  r=subprocess.run(aeneas,cwd=S,env=env);record['aeneas_exit']=r.returncode
 record['exit']=r.returncode
finally:
 record['lock_after']=sha(S/'Cargo.lock');assert record['lock_after']==frozen
 record['outputs']={str(p.relative_to(O)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in O.rglob('*') if p.is_file()}
 (B/'NJZ_EXTRACT_PINS.json').write_text(json.dumps(record,indent=2)+'\n')
sys.exit(r.returncode)
