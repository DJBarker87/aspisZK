#!/usr/bin/env python3
"""Accepted paired SDK parent context, with explicit verified-callee cuts.
The native AccountInfo stage1 body is copied verbatim. Expensive pure child
results are full typed shared replies; only the native std-any GOTO body is
abstracted later. This packet does not itself instantiate the callee joins.
"""
from pathlib import Path
import sys,subprocess,hashlib,json,tempfile
R=Path(__file__).resolve().parents[2];O=Path(sys.argv[1]);mode=sys.argv[2] if len(sys.argv)>2 else 'paired';assert mode in ['paired','native','prefix','call'];(O/'src').mkdir(exist_ok=True,parents=True)
freeze='b2727acd3abf79315d18b754a260f58f4b1c6326'
frozen=subprocess.check_output(['git','-C',str(R),'show',freeze+':programs/r1-cost-probe/src/r1_pool_adapter.rs'],text=True)
def cut(s,name):
 a=s.index('fn '+name);i=s.index('{',a)+1;depth=1
 while depth:depth+=(s[i]=='{')-(s[i]=='}');i+=1
 return s[a:i]
base=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/modular-host/sources/owned-sdk-v3/src/lib.rs'
raw=base.read_text();prefix=raw[:raw.index('#[derive(Clone,Copy)]\npub struct OwnedAccount')]
names=['readonly_buffer_meta_ok','require_readonly_buffer','require_verifier_checkpoint','require_distinct_accounts','stage1']
body='\n'.join(cut(frozen,name) for name in names)
# Preserve all original native guard/caller code and the exact first_decoded.
s=prefix+'''
use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalCommonV1,PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1,PoolV1PairVerifiedAfterstateV1,PoolV1PairForestTerminalFormatErrorV1,PoolV1PairVerifierTransportErrorV1};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
mod adapter {use super::*;
'''+body+'''
pub fn run(program:&Pubkey,accounts:&[AccountInfo<'_>],data:&[u8])->ProgramResult {stage1(program,accounts,data)}
}
#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk_snapshots::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};
#[derive(Clone,Copy)] struct Plan {statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],output:[u8;1769],output_len:usize,k:usize}
static mut PLAN:Option<Plan>=None;
static mut PHASE:usize=0;
static mut CALLS:[[u8;4];2]=[[0;4];2];
static mut NATIVE_ROOT_PTRS:[*const u8;3]=[core::ptr::null();3];
static mut MODEL_ROOT_PTRS:[*const u8;3]=[core::ptr::null();3];
static mut PUBLIC_SNAPSHOT_PTR:*const u8=core::ptr::null();
static mut PROOF_SNAPSHOT_PTR:*const u8=core::ptr::null();
static mut BOX_PTRS:[*const PoolV1PairForestTerminalStatementV1;2]=[core::ptr::null();2];
static mut CANDIDATE_PTRS:[*const PoolV1PairVerifiedAfterstateV1;2]=[core::ptr::null();2];
static mut PUBLIC_KIND:[u8;2]=[0;2];
static mut PUBLIC_PARTS:[[*const ();2];2]=[[core::ptr::null();2];2];
fn plan()->&'static Plan {unsafe{PLAN.as_ref().unwrap()}}
fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 if bytes.len()!=1880 {return Err(ProgramError::InvalidAccountData);}
 let phase=unsafe{PHASE};assert!(phase<2);
 let expected=if phase==0 {unsafe{NATIVE_ROOT_PTRS[1]}}else{unsafe{PUBLIC_SNAPSHOT_PTR}};
 assert_eq!(bytes.as_ptr(),expected);
 let boxed=Box::new(plan().statement);
 unsafe{BOX_PTRS[phase]=&*boxed;CANDIDATE_PTRS[phase]=&boxed.common().lane_transition.candidate_afterstate;CALLS[phase][0]+=1;}
 match boxed.semantic_public() {
  Public::Transfer(a,b)=>unsafe{PUBLIC_KIND[phase]=0;PUBLIC_PARTS[phase]=[a as *const _ as *const (),b as *const _ as *const ()];},
  Public::Withdrawal(a,b)=>unsafe{PUBLIC_KIND[phase]=1;PUBLIC_PARTS[phase]=[a as *const _ as *const (),b as *const _ as *const ()];},
 }
 Ok(boxed)
}
fn planned_validate(statement:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{
 let phase=unsafe{PHASE};assert_eq!(statement as *const _,unsafe{BOX_PTRS[phase]});unsafe{CALLS[phase][1]+=1;}Ok(())
}
fn planned_encode(afterstate:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{
 let phase=unsafe{PHASE};assert_eq!(afterstate as *const _,unsafe{CANDIDATE_PTRS[phase]});unsafe{CALLS[phase][2]+=1;}Ok(plan().candidate)
}
fn public_snapshot(bytes:&Vec<u8>)->Vec<u8>{
 assert_eq!(unsafe{PHASE},1);assert_eq!(bytes.len(),1880);assert_eq!(bytes.as_ptr(),unsafe{MODEL_ROOT_PTRS[1]});
 let output=bytes.clone();unsafe{PUBLIC_SNAPSHOT_PTR=output.as_ptr();}output
}
fn proof_snapshot(bytes:&Vec<u8>)->Vec<u8>{
 assert_eq!(unsafe{PHASE},1);assert_eq!(bytes.len(),58295);assert_eq!(bytes.as_ptr(),unsafe{MODEL_ROOT_PTRS[0]});
 let output=bytes.clone();unsafe{PROOF_SNAPSHOT_PTR=output.as_ptr();}output
}
fn planned_zero_scan(_:Vec<u8>)->bool {false}
fn planned_tx1<H:aspis_core::Digest32>(public:Public<'_>,bytes:&[u8],proof:&[u8],k:usize,_:H,observer:verifier::Observer)->Result<Vec<u8>,verifier::Error>{
 let phase=unsafe{PHASE};assert!(phase<2);assert!(observer.is_none());assert_eq!(k,plan().k);
 let expected_public=if phase==0{unsafe{NATIVE_ROOT_PTRS[1]}}else{unsafe{PUBLIC_SNAPSHOT_PTR}};
 let expected_proof=if phase==0{unsafe{NATIVE_ROOT_PTRS[0]}}else{unsafe{PROOF_SNAPSHOT_PTR}};
 assert_eq!(bytes.as_ptr(),expected_public);assert_eq!(bytes.len(),1880);
 assert_eq!(proof.as_ptr(),unsafe{expected_proof.add(688)});assert_eq!(proof.len(),57607);
 match public {
  Public::Transfer(a,b)=>{assert_eq!(unsafe{PUBLIC_KIND[phase]},0);assert_eq!(a as *const _ as *const (),unsafe{PUBLIC_PARTS[phase][0]});assert_eq!(b as *const _ as *const (),unsafe{PUBLIC_PARTS[phase][1]});},
  Public::Withdrawal(a,b)=>{assert_eq!(unsafe{PUBLIC_KIND[phase]},1);assert_eq!(a as *const _ as *const (),unsafe{PUBLIC_PARTS[phase][0]});assert_eq!(b as *const _ as *const (),unsafe{PUBLIC_PARTS[phase][1]});},
 }
 unsafe{CALLS[phase][3]+=1;}
 Ok(plan().output[..plan().output_len].to_vec())
}
'''
harness=(R/'tools/s126-sdk-20261021/harness.rs').read_text();start=harness.index('fn statement()');end=harness.index('\n#[kani::proof]',start)
if len(sys.argv)>3 and sys.argv[3]=='fields':
 with tempfile.TemporaryDirectory() as d:
  subprocess.run(['python3',str(R/'tools/s126-sdk-modular-20261021/make-sdk-statement-fields.py'),d],check=True)
  s+=(Path(d)/'statement.rs').read_text()
  (O/'statement-fields.json').write_bytes((Path(d)/'statement-fields.json').read_bytes())
else:s+=harness[start:end]+'\n'
s+=r'''
#[kani::proof] #[kani::unwind(1772)]
#[kani::stub(crate::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_snapshots::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,planned_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,planned_encode)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx1,planned_tx1)]
#[kani::stub(aspis_s126_owned_sdk_snapshots::public_snapshot,public_snapshot)]
#[kani::stub(aspis_s126_owned_sdk_snapshots::proof_snapshot,proof_snapshot)]
#[kani::stub(aspis_s126_owned_sdk_snapshots::owned_checkpoint_nonzero,planned_zero_scan)]
fn paired_parent_context() {
 let program=Pubkey::new_from_array(kani::any());
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);
 let output_len:usize=kani::any();kani::assume(output_len<=1769);
 unsafe{PLAN=Some(Plan{statement:statement(),candidate:kani::any(),output:kani::any(),output_len,k:instruction[1] as usize});}
 let mut b0:[u8;58295]=kani::any();let mut b1:[u8;1880]=kani::any();let mut b2:[u8;1768]=kani::any();
 b0[..688].copy_from_slice(&plan().candidate);b0[696]=2;
 let snapshots=[b0.to_vec(),b1.to_vec(),b2.to_vec()];
 unsafe{NATIVE_ROOT_PTRS=[b0.as_ptr(),b1.as_ptr(),b2.as_ptr()];MODEL_ROOT_PTRS=core::array::from_fn(|i|snapshots[i].as_ptr());}
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;let [ref mut l0,ref mut l1,ref mut l2]=amounts;
 let mut accounts=[
  AccountInfo::new(&keys[0],flags[0][0],flags[0][1],l0,&mut b0,&owners[0],flags[0][2],rents[0]),
  AccountInfo::new(&keys[1],flags[1][0],flags[1][1],l1,&mut b1,&owners[1],flags[1][2],rents[1]),
  AccountInfo::new(&keys[2],flags[2][0],flags[2][1],l2,&mut b2,&owners[2],flags[2][2],rents[2]),
 ];
 let data_roots=[accounts[0].data.clone(),accounts[1].data.clone(),accounts[2].data.clone()];
 let lamport_roots=[accounts[0].lamports.clone(),accounts[1].lamports.clone(),accounts[2].lamports.clone()];
 let data_slots:[usize;3]=kani::any();let lamport_slots:[usize;3]=kani::any();
 for i in 0..3 {kani::assume(data_slots[i]<3);kani::assume(lamport_slots[i]<3);accounts[i].data=data_roots[data_slots[i]].clone();accounts[i].lamports=lamport_roots[lamport_slots[i]].clone();}
 let initial_counts:[isize;3]=kani::any();let initial_lamport_counts:[isize;3]=kani::any();
 let counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&data_roots[i]).cast::<std::cell::Cell<isize>>());
 let lamport_counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<std::cell::Cell<isize>>());
 for i in 0..3 {assert_eq!(unsafe{(*counters[i]).get()},0);assert_eq!(unsafe{(*lamport_counters[i]).get()},0);unsafe{(*counters[i]).set(initial_counts[i]);(*lamport_counters[i]).set(initial_lamport_counts[i]);}}
 let model=OwnedSdk{
  accounts:(0..3).map(|i|OwnedAccount{key:keys[i].to_bytes(),owner:owners[i].to_bytes(),is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:data_slots[i],lamports_slot:lamport_slots[i]}).collect(),
  data_cells:snapshots.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:initial_counts[i],strong:std::rc::Rc::strong_count(&data_roots[i]),weak:std::rc::Rc::weak_count(&data_roots[i])}).collect(),
  lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:initial_amounts[i],borrowed:initial_lamport_counts[i],strong:std::rc::Rc::strong_count(&lamport_roots[i]),weak:std::rc::Rc::weak_count(&lamport_roots[i])}).collect(),
 };
 unsafe{PHASE=0;CALLS=[[0;4];2];}
 let actual=adapter::run(&program,&accounts,&instruction[..instruction_len]);
 if actual.is_ok() {
  // Explicit accepted context: pure child replies are common typed values.
  unsafe{PHASE=1;}
  let (expected,model)=aspis_s126_owned_sdk_snapshots::owned_stage1(program.to_bytes(),model,instruction[..instruction_len].to_vec());
  assert!(expected.is_ok());
  for phase in 0..2 {for event in 0..4 {assert_eq!(unsafe{CALLS[phase][event]},1);}}
  assert_eq!(plan().output_len,1768);
  assert_eq!(data_slots,[0,1,2]);
  let observed:usize=kani::any();kani::assume(observed<1768);
  let checkpoint=accounts[2].try_borrow_data().unwrap();
  assert_eq!(checkpoint[observed],plan().output[observed]);assert_eq!(model.data_cells[2].bytes[observed],checkpoint[observed]);drop(checkpoint);
  for i in 0..3 {
   assert_eq!(model.accounts[i].key,accounts[i].key.to_bytes());assert_eq!(model.accounts[i].owner,accounts[i].owner.to_bytes());
   assert_eq!(model.accounts[i].is_signer,accounts[i].is_signer);assert_eq!(model.accounts[i].is_writable,accounts[i].is_writable);
   assert_eq!(model.accounts[i].executable,accounts[i].executable);assert_eq!(model.accounts[i].rent_epoch,accounts[i].rent_epoch);
   assert_eq!(model.accounts[i].data_slot,data_slots[i]);assert_eq!(model.accounts[i].lamports_slot,lamport_slots[i]);
   assert_eq!(unsafe{(*counters[i]).get()},model.data_cells[i].borrowed);assert_eq!(model.data_cells[i].borrowed,initial_counts[i]);
   assert_eq!(unsafe{(*lamport_counters[i]).get()},model.lamports_cells[i].borrowed);assert_eq!(model.lamports_cells[i].borrowed,initial_lamport_counts[i]);
   assert_eq!(model.lamports_cells[i].amount,initial_amounts[i]);
   assert_eq!(model.data_cells[i].strong,std::rc::Rc::strong_count(&data_roots[i]));assert_eq!(model.data_cells[i].weak,std::rc::Rc::weak_count(&data_roots[i]));
   assert_eq!(model.lamports_cells[i].strong,std::rc::Rc::strong_count(&lamport_roots[i]));assert_eq!(model.lamports_cells[i].weak,std::rc::Rc::weak_count(&lamport_roots[i]));
  }
 }
 for i in 0..3 {unsafe{(*counters[i]).set(0);(*lamport_counters[i]).set(0);}}
 kani::cover!(actual.is_ok(),"paired parent accepts with full arbitrary checkpoint bytes");
 kani::cover!(actual.is_ok()&&matches!(plan().statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}),"withdrawal parent accepts");
}
}
'''
if mode in ['native','prefix','call']:
 # Same frozen complete SDK caller. Remove only reference invocation/state;
 # assertions inspect every reached typed child argument in the native path.
 s=s.replace('fn paired_parent_context()', 'fn native_parent_arguments()')
 s=s.replace(' let snapshots=[b0.to_vec(),b1.to_vec(),b2.to_vec()];', '')
 s=s.replace('MODEL_ROOT_PTRS=core::array::from_fn(|i|snapshots[i].as_ptr());', '')
 a=s.index(' let model=OwnedSdk{');b=s.index(' unsafe{PHASE=0;CALLS=[[0;4];2];}',a)
 s=s[:a]+s[b:]
 a=s.index(' if actual.is_ok() {');b=s.index(' for i in 0..3 {unsafe{(*counters[i]).set(0);',a)
 s=s[:a]+r"""
 if actual.is_ok() {
  for event in 0..4 {assert_eq!(unsafe{CALLS[0][event]},1);}
  assert_eq!(plan().output_len,1768);assert_eq!(data_slots,[0,1,2]);
  let observed:usize=kani::any();kani::assume(observed<1768);
  let checkpoint=accounts[2].try_borrow_data().unwrap();
  assert_eq!(checkpoint[observed],plan().output[observed]);drop(checkpoint);
 }
 for i in 0..3 {
  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);
  assert_eq!(unsafe{(*lamport_counters[i]).get()},initial_lamport_counts[i]);
 }
"""+s[b:]
 s=s.replace('paired parent accepts with full arbitrary checkpoint bytes','native caller accepts with full arbitrary checkpoint bytes')
 s=s.replace('withdrawal parent accepts','withdrawal native caller accepts')
if mode=='call':
 s=s.replace('fn native_parent_arguments()', 'fn call_parent_arguments()')
 s=s.replace('output:kani::any(),output_len,k:instruction[1] as usize', 'output:[0;1769],output_len:0,k:instruction[1] as usize')
 a=s.index(' if actual.is_ok() {');b=s.index(' for i in 0..3 {\n  assert_eq!',a)
 s=s[:a]+' assert!(actual.is_err());\n assert!(unsafe{CALLS[0][3]}<=1);\n'+s[b:]
 a=s.index(' kani::cover!(actual.is_ok(),');b=s.index('\n}\n}',a)
 s=s[:a]+''' kani::cover!(unsafe{CALLS[0][3]}==1,"full real SDK caller reaches tx1 with exact same-object/public/proof/k/None arguments");
 kani::cover!(unsafe{CALLS[0][3]}==1&&matches!(plan().statement,PoolV1PairForestTerminalStatementV1::Withdrawal{..}),"withdrawal SDK caller reaches tx1");'''+s[b:]
if mode=='prefix':
 s=s.replace('fn native_parent_arguments()', 'fn prefix_parent_arguments()')
 old=cut(s,'planned_decode')
 s=s.replace(old,r"""fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
  if bytes.len()!=1880 {return Err(ProgramError::InvalidAccountData);}
  assert_eq!(bytes.as_ptr(),unsafe{NATIVE_ROOT_PTRS[1]});
  unsafe{CALLS[0][0]+=1;}
  Err(ProgramError::InvalidAccountData)
 }""")
 s=s.replace(' b0[..688].copy_from_slice(&plan().candidate);b0[696]=2;', '')
 s=s.replace(' unsafe{PLAN=Some(Plan{statement:statement(),candidate:kani::any(),output:kani::any(),output_len,k:instruction[1] as usize});}', '')
 a=s.index(' if actual.is_ok() {');b=s.index(' for i in 0..3 {\n  assert_eq!',a)
 s=s[:a]+' assert!(actual.is_err());\n assert!(unsafe{CALLS[0][0]}<=1);\n'+s[b:]
 a=s.index(' kani::cover!(actual.is_ok(),');b=s.index('\n}\n}',a)
 s=s[:a]+' kani::cover!(unsafe{CALLS[0][0]}==1,"full source prefix reaches decoder with exact native public buffer");'+s[b:]
if len(sys.argv)>4 and sys.argv[4]=='unreachable-error':
 s=s.replace('fn planned_zero_scan(_:Vec<u8>)->bool {false}', 'fn planned_zero_scan(_:Vec<u8>)->bool {false}\nfn unreachable_error(_:verifier::Error)->ProgramError {assert!(false,"successful verifier reply never calls error mapper");ProgramError::InvalidInstructionData}')
 s=s.replace('#[kani::proof] #[kani::unwind(1772)]', '#[kani::stub(crate::error,unreachable_error)]\n#[kani::proof] #[kani::unwind(1772)]')
 if mode=='paired':s=s.replace('#[kani::stub(crate::error,unreachable_error)]', '#[kani::stub(crate::error,unreachable_error)]\n#[kani::stub(aspis_s126_owned_sdk_snapshots::error,unreachable_error)]')
(O/'src/lib.rs').write_text(s)
host='/home/dombarker/project-offloads/codex-cx-repin-s6-20261020/src'
(O/'Cargo.toml').write_text('''[package]
name="aspis-s126-sdk-CONTEXT-context-v1"
version="0.0.0"
edition="2021"
[workspace]
[dependencies]
solana-program="=2.3.0"
aspis-core={path="ROOT/crates/aspis-core",features=["r0"]}
aspis-statement={path="ROOT/crates/aspis-statement",features=["r0","pool-v1-kernel"]}
aspis-r1-cost-probe={path="ROOT/crates/aspis-r1-cost-probe",features=["optimized-terminal","program-build"]}
aspis-s126-owned-sdk-snapshots={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/owned-sdk-snapshots-v1"}
[profile.release]
opt-level=3
overflow-checks=true
'''.replace('ROOT',host).replace('CONTEXT',mode))
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',freeze=freeze,source_sha256=sha(s),context_mode=mode,native_functions={n:dict(source=cut(frozen,n),sha256=sha(cut(frozen,n))) for n in names},qualification=__doc__,domain='Three real AccountInfo values, independent data/lamport alias maps and every signed data/lamport count. Root buffers hold all58295/1880/1768-byte values. Both full typed statement variants and all field bit patterns, arbitrary encoded688-byte candidate and all1769 output bytes; returned child length0..1769. Native successful run must imply successful reference run, exact decoded-object/semantic-reference/public/proof/k/None arguments, once-only call order, checkpoint cell equality and complete SDK metadata/counter state. Assertions are accepted-only; broader rejected buffer/SDK effects are checked by the separate heap/lifecycle certificates.',retained_cuts=['common full-typed successful decoder/validator/encoder/verifier child replies; actual child joins must be instantiated','native std-any GOTO function may be overapproximated only with explicit symbol/tool pins; reference scan false requires native-accepted scan/byte-view composition','pure snapshot helpers keep the identical Vec clone plus ghost pointer observers','allocation/SDK/compiler/runtime P2/P6 boundaries; no whole source or global join completion from codegen or this context alone']),indent=2)+'\n')

if mode=='prefix':
 p=O/'source-cut.json';cutmeta=json.loads(p.read_text())
 cutmeta['qualification']='Actual complete frozen native stage1 with a decoder-entry cut returning InvalidAccountData. The prefix must preserve the exact admitted decoder input pointer/length, once-only admitted entry, all data/lamport counter restoration, and error return. Full typed child construction is unreachable and removed from the harness, not from the frozen stage1. No accepted/full-stage claim.'
 cutmeta['domain']='Three real AccountInfo values, independent data/lamport alias maps and all signed counters/metadata; arbitrary58295/1880/1768-byte root buffers. Native std-any is the only GOTO overapproximation. The decoder stub retains its actual1880-byte length rejection, then asserts the admitted public root pointer and returns a fixed source error. No decoder success or semantic object premise.'
 cutmeta['retained_cuts']=['Actual std-any scan/byte-view certificate must be composed; its nondeterministic overapproximation covers both results','Runtime heap embedding and compiler/library boundaries','Complete post-decoder continuation is excluded from this prefix check']
 p.write_text(json.dumps(cutmeta,indent=2)+'\n')

if len(sys.argv)>4 and sys.argv[4]=='unreachable-error':
 p=O/'source-cut.json';m=json.loads(p.read_text())
 m['retained_cuts'].append('Error mapper has an assert-false reachability stub: the context must prove it is never called with the common successful verifier reply. No error mapping/log implementation equality is asserted for rejected verifier children.')
 m['statement_factory']='Every real struct field generated from frozen declarations; both variants, all u32 M31 storage words, no canonicality restriction. Padding is not a value field.'
 p.write_text(json.dumps(m,indent=2)+'\n')

if mode=='call':
 p=O/'source-cut.json';m=json.loads(p.read_text())
 m['qualification']='Native tx1-entry prefix certificate. Full frozen SDK stage1 and full typed statement/candidate callbacks are retained; tx1 returns a fixed successful empty vector, forcing the following length guard to reject. Assertions at child entry prove actual pointer/semantic-reference/k/None arguments independent of later returned bytes. Counter restoration is checked on every return. No accepted-parent or writeback claim.'
 m['domain']='Arbitrary native metadata, independent alias maps and all signed counters; full1880/1768 public/checkpoint root byte values. Proof root bytes are arbitrary subject to its first688 bytes equalling the arbitrary candidate reply and byte696 being the S2 tag2, matching the admitted source prefix/tag guard; mismatching prefix/tag paths are not covered by this cut. Every value field of both actual statement variants is quantified. Actual decoder length rejection retained. The tx1 reply is fixed successful-empty; no post-child or total execution theorem is inferred.'
 m['retained_cuts'].append('tx1-entry context returns Ok(empty Vec) after checking arguments; native execution prefix/callee-interpretation transport must be composed to use this for other replies')
 p.write_text(json.dumps(m,indent=2)+'\n')
