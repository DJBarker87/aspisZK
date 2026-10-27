"""Focused extraction of frozen library methods and owned safe references."""
from pathlib import Path
import subprocess,sys,json,shlex,re
root=Path(__file__).resolve().parents[2];stage=sys.argv[1]; variant=sys.argv[2] if len(sys.argv)>2 else 'op223-built'
assert stage in ('charon','aeneas')
base='/home/dombarker/project-offloads/codex-pv-cblib-20261027';gate='/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/src/tools/prover-rw-20261023/native-entropy';pinned='/home/dombarker/project-offloads/codex-pv-cb-20261026/pinned-tools'
entries={
'array-slice-result-opt':('pv_cblib_source::array_slice_result_reference','pv_cblib_source::array_slice_result_reference+pv_cblib_source::array_reference','PV_CBL_ArraySliceResult'),
'sha-update-soft-opt':('pv_cblib_source::sha_digest_soft_owned', 'pv_cblib_source::sha_finalize_soft_owned+pv_cblib_source::sha_compress_byte_owned+pv_cblib_source::sha_digest32+pv_cblib_source::sha_length_suffix64+pv_cblib_source::sha_load64+pv_cblib_source::sha_load_be4+pv_cblib_source::sha_store_be4+pv_cblib_source::sha_pad_owned_split8+pv_cblib_source::sha_pad_zero+pv_cblib_source::sha_pad_suffix8+pv_cblib_source::sha_load_lane0+pv_cblib_source::sha_load_lane1+pv_cblib_source::sha_load_lane2+pv_cblib_source::sha_load_lane3+pv_cblib_source::sha_load_lane4+pv_cblib_source::sha_load_lane5+pv_cblib_source::sha_load_lane6+pv_cblib_source::sha_load_lane7+pv_cblib_source::sha_load_lane8+pv_cblib_source::sha_load_lane9+pv_cblib_source::sha_load_lane10+pv_cblib_source::sha_load_lane11+pv_cblib_source::sha_load_lane12+pv_cblib_source::sha_load_lane13+pv_cblib_source::sha_load_lane14+pv_cblib_source::sha_load_lane15+pv_cblib_source::sha_fallback_reference::_+pv_cblib_source::sha_fallback_consts::_+pv_cblib_source::sha_update_soft_owned+pv_cblib_source::sha_default_soft_owned+pv_cblib_source::sha_digest_soft_owned', 'PV_CBL_DigestSoft'),
'sha-final-soft-opt':('pv_cblib_source::sha_finalize_soft_owned','pv_cblib_source::sha_finalize_soft_owned+pv_cblib_source::sha_compress_byte_owned+pv_cblib_source::sha_digest32+pv_cblib_source::sha_length_suffix64+pv_cblib_source::sha_load64+pv_cblib_source::sha_load_be4+pv_cblib_source::sha_store_be4+pv_cblib_source::sha_pad_owned_split8+pv_cblib_source::sha_pad_zero+pv_cblib_source::sha_pad_suffix8+pv_cblib_source::sha_load_lane0+pv_cblib_source::sha_load_lane1+pv_cblib_source::sha_load_lane2+pv_cblib_source::sha_load_lane3+pv_cblib_source::sha_load_lane4+pv_cblib_source::sha_load_lane5+pv_cblib_source::sha_load_lane6+pv_cblib_source::sha_load_lane7+pv_cblib_source::sha_load_lane8+pv_cblib_source::sha_load_lane9+pv_cblib_source::sha_load_lane10+pv_cblib_source::sha_load_lane11+pv_cblib_source::sha_load_lane12+pv_cblib_source::sha_load_lane13+pv_cblib_source::sha_load_lane14+pv_cblib_source::sha_load_lane15+pv_cblib_source::sha_fallback_reference::_+pv_cblib_source::sha_fallback_consts::_','PV_CBL_FinalSoft'),
'sha-digest32-opt':('pv_cblib_source::sha_digest32','pv_cblib_source::sha_digest32+pv_cblib_source::sha_store_be4','PV_CBL_Digest32'),
'sha-suffix64-opt':('pv_cblib_source::sha_length_suffix64','pv_cblib_source::sha_length_suffix64','PV_CBL_Suffix64'),
'pop-resize-opt':('pv_cblib_source::pop_copy_resize_reference','pv_cblib_source::pop_copy_resize_reference','PV_CBL_PopResize'),
'join-resize-opt':('pv_cblib_source::join_resize_reference','pv_cblib_source::join_resize_reference','PV_CBL_JoinResize'),
'sha-bytes-opt':('pv_cblib_source::sha_byte_codec_root','pv_cblib_source::sha_byte_codec_root+pv_cblib_source::sha_load_lane0+pv_cblib_source::sha_load_lane1+pv_cblib_source::sha_load_lane2+pv_cblib_source::sha_load_lane3+pv_cblib_source::sha_load_lane4+pv_cblib_source::sha_load_lane5+pv_cblib_source::sha_load_lane6+pv_cblib_source::sha_load_lane7+pv_cblib_source::sha_load_lane8+pv_cblib_source::sha_load_lane9+pv_cblib_source::sha_load_lane10+pv_cblib_source::sha_load_lane11+pv_cblib_source::sha_load_lane12+pv_cblib_source::sha_load_lane13+pv_cblib_source::sha_load_lane14+pv_cblib_source::sha_load_lane15+pv_cblib_source::sha_load_be4+pv_cblib_source::sha_load64+pv_cblib_source::sha_store_be4','PV_CBL_ShaBytes'),
'sha-pad-fixed-opt':('pv_cblib_source::sha_pad_owned_split8','pv_cblib_source::sha_pad_owned_split8+pv_cblib_source::sha_pad_zero+pv_cblib_source::sha_pad_suffix8','PV_CBL_ShaPadFixed'),
'sha-pad-split-opt':('pv_cblib_source::sha_pad_owned_split','pv_cblib_source::sha_pad_owned_split+pv_cblib_source::sha_pad_zero+pv_cblib_source::sha_pad_suffix','PV_CBL_ShaPadSplit'),
'sha-pad-owned-opt':('pv_cblib_source::sha_pad_owned','pv_cblib_source::sha_pad_owned','PV_CBL_ShaPadOwned'),
'core-new-owned-opt':('pv_cblib_source::sha_core_new_owned','pv_cblib_source::sha_core_new_owned','PV_CBL_CoreNewOwned'),
'op30-bytes-opt':('pv_cblib_source::string_capacity_bytes_reference','pv_cblib_source::string_capacity_bytes_reference','PV_CBL_StringCapacityBytes'),
'op31-bytes-opt':('pv_cblib_source::push_bytes_reference','pv_cblib_source::push_bytes_reference','PV_CBL_StringPushBytes'),
'op30-default-opt':('pv_cblib_source::string_default_reference','pv_cblib_source::string_default_reference+alloc::string::_::default','PV_CBL_StringDefaultReference'),
'op33-borrow-opt':('pv_cblib_source::pop_reference','pv_cblib_source::pop_reference','PV_CBL_PopBorrowReference'),
'fallback-four-opt':('pv_cblib_source::sha_fallback_reference::extracted_round4','pv_cblib_source::sha_fallback_reference::_','PV_CBL_FallbackFour'),
'op217-mono':('pv_cblib_source::sha_default','pv_cblib_source::sha_default+digest::core_api::wrapper::_::default+digest::core_api::ct_variable::_::default+sha2::core_api::_::new+block_buffer::_::default+generic_array::_::default','PV_CBL_Op217Mono'),
'fallback-block-opt':('pv_cblib_source::sha_fallback_reference::extracted_block','pv_cblib_source::sha_fallback_reference::_+pv_cblib_source::sha_fallback_consts::_','PV_CBL_FallbackBlock'),
'op36-retain-opt':('pv_cblib_source::array_retained_reference','pv_cblib_source::array_retained_reference+pv_cblib_source::array_reference','PV_CBL_ArrayRetainedReference'),
'op33-retain-opt':('pv_cblib_source::pop_retained_reference','pv_cblib_source::pop_retained_reference','PV_CBL_PopRetainedReference'),
'fallback-round-opt':('pv_cblib_source::sha_fallback_reference::extracted_round','pv_cblib_source::sha_fallback_reference::extracted_round+pv_cblib_source::sha_fallback_reference::sha256_digest_round_x2','PV_CBL_FallbackRound'),
'fallback-schedule-opt':('pv_cblib_source::sha_fallback_reference::extracted_schedule','pv_cblib_source::sha_fallback_reference::_','PV_CBL_FallbackSchedule'),
'sha-round-opt':('sha2::sha256::soft::sha256_digest_round_x2','sha2::sha256::soft::sha256_digest_round_x2','PV_CBL_ShaRound'),
'sha-schedule-opt':('sha2::sha256::soft::schedule','sha2::sha256::soft::schedule+sha2::sha256::soft::sha256msg1+sha2::sha256::soft::sha256msg2+sha2::sha256::soft::sha256load+sha2::sha256::soft::shl+sha2::sha256::soft::shr+sha2::sha256::soft::xor+sha2::sha256::soft::or+sha2::sha256::soft::add','PV_CBL_ShaSchedule'),
'op30-ref-new-opt':('pv_cblib_source::string_capacity_reference','pv_cblib_source::string_capacity_reference+alloc::string::_::new','PV_CBL_StringNewReference'),
'join-mut-opt':('pv_cblib_source::join_mut_reference','pv_cblib_source::join_mut_reference','PV_CBL_JoinMutReference'),
'sha-dispatch-opt':('sha2::sha256::compress256','sha2::sha256::compress256+sha2::sha256::x86::_+sha2::sha256::soft::_','PV_CBL_ShaDispatch'),
'sha-fallback-opt':('sha2::sha256::soft::compress','sha2::sha256::soft::_+sha2::consts::K32X4+sha2::consts::BLOCK_LEN','PV_CBL_ShaFallback'),
'op30-ref-opt':('pv_cblib_source::string_capacity_reference','pv_cblib_source::string_capacity_reference','PV_CBL_StringCapacityReference'),
'string-owned-opt':('pv_cblib_source::string_owned_reference','pv_cblib_source::string_owned_reference','PV_CBL_StringOwnedReference'),
'join-ref-opt':('pv_cblib_source::join_bytes_reference','pv_cblib_source::join_bytes_reference','PV_CBL_JoinBytesReferenceOpt'),
'op30-opt':('pv_cblib_source::string_capacity','alloc::string::_::with_capacity','PV_CBL_Op30Opt'),
'op31-opt':('pv_cblib_source::string_push','alloc::string::_::push_str','PV_CBL_Op31Opt'),
'op217-core-new-opt':('pv_cblib_source::sha_core_new','sha2::core_api::{impl digest::core_api::VariableOutputCore for sha2::core_api::Sha256VarCore}::new+sha2::core_api::Sha256VarCore+sha2::consts::H256_224+sha2::consts::H256_256','PV_CBL_ShaCoreNew'),
'op33-exact-opt':('aspis_r1_cost_probe::host_commitment::pv_cblib_library_checks::pop_owned_reference','aspis_r1_cost_probe::host_commitment::pv_cblib_library_checks::pop_owned_reference+aspis_r1_cost_probe::host_commitment::pv_cblib_library_checks::copy_result_reference','PV_CBL_Op33ExactReference'),
'op36-owned-opt':('pv_cblib_source::array_result_reference','pv_cblib_source::array_reference+pv_cblib_source::array_qm31_reference+pv_cblib_source::array_result_reference','PV_CBL_Op36OwnedReference'),
'op36-full-opt':('pv_cblib_source::array_full_reference','pv_cblib_source::array_reference+pv_cblib_source::array_qm31_reference+pv_cblib_source::array_full_reference+aspis_core::field::QM31::ZERO+aspis_core::field::{impl core::clone::Clone for aspis_core::field::QM31}::clone+aspis_core::field::{impl core::clone::Clone for aspis_core::field::CM31}::clone+aspis_core::field::{impl core::clone::Clone for aspis_core::field::M31}::clone','PV_CBL_Op36FullReference'),
'op215-mono':('pv_cblib_source::sha_finalize_into','digest::core_api::wrapper::{impl digest::FixedOutput for _}::finalize_into+digest::core_api::wrapper::CoreWrapper','PV_CBL_Op215Mono'),
'op209-ref-opt':('pv_cblib_source::split_owned_reference','pv_cblib_source::split_owned_reference','PV_CBL_Op209Reference'),
'op36-qm31-opt':('pv_cblib_source::array_qm31_reference','pv_cblib_source::array_reference+pv_cblib_source::array_qm31_reference','PV_CBL_Op36QM31Reference'),
'path-owned-opt':('pv_cblib_source::path_owned_reference','pv_cblib_source::path_owned_reference','PV_CBL_PathOwnedReference'),
'join-ref':('pv_cblib_source::join_bytes_reference','pv_cblib_source::join_bytes_reference','PV_CBL_JoinBytesReference'),
'op33-owned-opt':('pv_cblib_source::pop_owned_reference','pv_cblib_source::pop_owned_reference','PV_CBL_Op33OwnedReference'),
'op36-ref-opt':('pv_cblib_source::array_reference','pv_cblib_source::array_reference','PV_CBL_Op36Reference'),
'path-ref-opt':('pv_cblib_source::path_bytes_reference','pv_cblib_source::path_bytes_reference','PV_CBL_PathBytesReference'),
'op205-opt':('pv_cblib_source::sha_finalize_variable','sha2::core_api::{impl digest::core_api::VariableOutputCore for sha2::core_api::Sha256VarCore}::finalize_variable_core+sha2::core_api::Sha256VarCore','PV_CBL_Op205Opt'),
'op208-opt':('pv_cblib_source::sha_update_blocks','sha2::core_api::{impl digest::core_api::UpdateCore for sha2::core_api::Sha256VarCore}::update_blocks+sha2::core_api::Sha256VarCore','PV_CBL_Op208Opt'),
'op215-opt':('pv_cblib_source::sha_finalize_into','digest::core_api::wrapper::{impl digest::FixedOutput for _}::finalize_into','PV_CBL_Op215Opt'),
'op216-opt':('pv_cblib_source::sha_update','digest::core_api::wrapper::{impl digest::Update for _}::update','PV_CBL_Op216Opt'),
'op217-opt':('pv_cblib_source::sha_default','digest::core_api::wrapper::{impl core::default::Default for _}::default','PV_CBL_Op217Opt'),
'op219-opt':('pv_cblib_source::sha_finalize_fixed','digest::core_api::ct_variable::{impl digest::core_api::FixedOutputCore for _}::finalize_fixed_core','PV_CBL_Op219Opt'),
'op35-opt':('pv_cblib_source::vec_default','alloc::vec::{impl core::default::Default for alloc::vec::Vec<_>}::default','PV_CBL_Op35Opt'),
'op212-opt':('pv_cblib_source::finalize','digest::digest::_::finalize+digest::FixedOutput::finalize_fixed','PV_CBL_Op212Opt'),
'op212':('{impl digest::digest::Digest for _}::finalize','digest::digest::{impl digest::digest::Digest for _}::finalize','PV_CBL_Op212'),
'op34-ref':('pv_cblib_source::empty_reference','pv_cblib_source::empty_reference','PV_CBL_Op34Reference'),
'op35-ref':('pv_cblib_source::default_reference','pv_cblib_source::default_reference','PV_CBL_Op35Reference'),
'op33-ref':('pv_cblib_source::pop_reference','pv_cblib_source::pop_reference','PV_CBL_Op33Reference'),
'op34':('pv_cblib_source::vec_empty','alloc::vec::_','PV_CBL_Op34'),
'op35':('pv_cblib_source::vec_default','alloc::vec::_::default','PV_CBL_Op35'),
'op33':('pv_cblib_source::vec_pop','alloc::vec::_::pop','PV_CBL_Op33'),
'op36':('pv_cblib_source::vec_array','core::array::_::try_from','PV_CBL_Op36'),
'op30':('pv_cblib_source::string_capacity','alloc::string::_::with_capacity','PV_CBL_Op30'),
'op31':('pv_cblib_source::string_push','alloc::string::_::push_str','PV_CBL_Op31'),
'op25':('pv_cblib_source::path_deref','std::path::_::deref','PV_CBL_Op25'),
'op29':('pv_cblib_source::path_asref','std::path::_::as_ref','PV_CBL_Op29'),
'op28':('pv_cblib_source::string_path','std::path::_::as_ref','PV_CBL_Op28'),
'op26':('pv_cblib_source::path_join','std::path::Path::join','PV_CBL_Op26'),
}
assert variant in entries
m=re.match(r'op(\d+)',variant)
op=int(m[1]) if m else (26 if variant in ('join-ref','join-ref-opt') else 25)
subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/precheck.py'),str(op)],check=True)
entry,include,namespace=entries[variant]
name=stage+'-source-'+variant+'-'+(sys.argv[3] if len(sys.argv)>3 else '001')
out=root/'evidence/pv-cblib-20261027'/name;out.mkdir(exist_ok=True)

def ssh(c):return subprocess.run(['ssh','dombarker@100.108.41.90',c],text=True,capture_output=True)
r=ssh(f'mkdir -p {base}/{name}; python3 {gate}/reservation.py {base}/{name}/admission-before.json > {base}/{name}/reservation.log 2>&1; cat {base}/{name}/reservation.log');(out/'admission-transport.log').write_text(r.stdout+r.stderr)
if not json.loads(r.stdout)['allowed']:print('REFUSED');sys.exit(78)
if stage=='charon':
 args=['timeout','120',*(['taskset','--cpu-list','0-3'] if variant=='op33-exact-opt' else []),'env','PATH=/home/dombarker/.cargo/bin:/usr/local/bin:/usr/bin:/bin','RUSTUP_TOOLCHAIN=nightly-2026-06-01','RUSTFLAGS=--cfg pv_cb_extract',f'CARGO_TARGET_DIR={base}/charon-target',pinned+'/charon','cargo','--preset','aeneas',*(['--hide-allocator'] if True else []),*(['--monomorphize','--precise-drops','--desugar-drops'] if variant.endswith('-mono') else []),'--mir',('optimized' if variant.endswith(('-opt','-mono')) else 'built'),'--rustc-arg=--cfg=kani','--rustc-arg=--cfg=pv_cb_extract','--sysroot','default','--start-from',entry,*sum((['--include',x] for x in include.split('+')),[]),*(['--opaque','alloc::vec::Vec','--opaque','alloc::vec::_::new','--opaque','alloc::vec::_::len','--opaque','alloc::vec::_::remove'] if variant in ('op34','op35','op35-opt','op33','op36','op34-ref','op35-ref','op33-ref','op33-owned-opt') else []),'--dest-file',base+'/'+namespace+'.llbc','--','--manifest-path',base+('/source/crates/aspis-r1-cost-probe/Cargo.toml' if variant=='op33-exact-opt' else '/source-proof/Cargo.toml'),*(['--features','ct-host-prover'] if variant=='op33-exact-opt' else []),'--release','--offline','--lib','--jobs','4']
else:
 # Charon can exit zero while marking the translated crate invalid.
 validity=ssh('python3 -c '+shlex.quote('import json;print(json.load(open('+repr(base+'/'+namespace+'.llbc')+')).get("has_errors"))'))
 (out/'llbc-error-preflight.log').write_text(validity.stdout+validity.stderr)
 if validity.returncode or validity.stdout.strip()!='False':
  print('REJECTED invalid LLBC; no Aeneas launch');sys.exit(2)
 args=['timeout','120',pinned+'/aeneas','-sequential','-no-progress-bar','-abort-on-error','-strict-joins','-backend','lean','-namespace',namespace,'-dest',base+'/'+variant+'-generated','-split-files','-emit-json',base+'/'+namespace+'.llbc']
 assert ssh(f'mkdir -p {base}/{variant}-generated').returncode==0
receipt=dict(target=args,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),expected_phase='optimized compilation / selected MIR extraction' if stage=='charon' else 'symbolic extraction of changed current-crate built MIR graph',print_axioms='N/A extraction',limits=dict(MemoryHigh='6G',MemoryMax='8G',MemorySwapMax=0,TasksMax=64))
assert not (out/'target.json').exists();(out/'target.json').write_text(json.dumps(receipt,indent=2)+'\n')
cmd=['systemd-run','--user','--scope','-p','MemoryHigh=6G','-p','MemoryMax=8G','-p','MemorySwapMax=0','-p','TasksMax=64','python3',gate+'/barrier.py',base+'/'+name+'/admission-barrier.json','/usr/bin/time','-v','-o',base+'/'+name+'/time.log',*args]
r=ssh(shlex.join(cmd)+f' > {base}/{name}/output.log 2>&1');(out/'transport.log').write_text(r.stdout+r.stderr)
subprocess.run([sys.executable,str(root/'tools/pv-cblib-20261027/collect_native.py'),name,'source-proof/lib.rs','source-proof/Cargo.toml','source/crates/aspis-r1-cost-probe/src/host_commitment.rs','source/crates/aspis-core/src/field.rs','source/crates/aspis-core/src/r0/mod.rs','kani-proof/lib.rs','kani-proof/reference.rs','kani-proof/Cargo.toml','source-proof/Cargo.lock',namespace+'.llbc',variant+'-generated/Funs.lean',variant+'-generated/Types.lean'],check=True)
p=out/'collected-receipt.json';r=json.loads(p.read_text());r.update(receipt);p.write_text(json.dumps(r,indent=2)+'\n');print(r['exit'])
sys.exit(int(r['exit']) if r['exit'] is not None else 78)
