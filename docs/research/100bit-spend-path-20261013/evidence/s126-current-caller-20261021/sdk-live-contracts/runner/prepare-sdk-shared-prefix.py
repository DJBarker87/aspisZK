#!/usr/bin/env python3
"""Actual native/complete borrowed-reference decoder-entry prefix on one heap.
The native call is verified to write only SDK borrow flags and decoder-hit
instrumentation before any reference reuse of its original owned byte buffers.
Native scan overapproximation and reached-decoder scope remain explicit.
"""
from pathlib import Path
import sys,json,hashlib
R=Path(__file__).resolve().parents[2];E=R/'docs/research/100bit-spend-path-20261013/evidence/s126-current-caller-20261021/sdk-parent-cuts'
O=Path(sys.argv[1]);(O/'src').mkdir(parents=True,exist_ok=False)
base=(E/'sources/sdk-native-context-v9/src/lib.rs').read_text();native=base[:base.index('#[cfg(kani)] mod proofs')]
rc=base[base.index(' // Reuse the pinned RcInner layout'):base.index(' let initial_counts:[isize;3]')]
rc=rc.replace(' let rc_counts:[[usize;4];3]=kani::any();\n for i in 0..3 {for j in 0..4 {kani::assume(rc_counts[i][j]>=1);}}\n','')
s=native+r'''
#[cfg(kani)] mod proofs {
use super::*;
use aspis_s126_owned_sdk_borrowed as owned;
use owned::{OwnedAccount,OwnedDataCell,OwnedLamportsCell,OwnedSdk};
use std::cell::Cell;
struct GhostStorage<T>{value:T,allocation_tag:u64}
static mut COUNTERS:GhostStorage<[*const Cell<isize>;3]>=GhostStorage{value:[core::ptr::null();3],allocation_tag:0x51a4000000000001};
static mut HITS:GhostStorage<[u8;2]>=GhostStorage{value:[0;2],allocation_tag:0x51a4000000000002};
static mut PHASE:GhostStorage<usize>=GhostStorage{value:0,allocation_tag:0x51a4000000000003};
static mut PUBLIC_PTR:GhostStorage<*const u8>=GhostStorage{value:core::ptr::null(),allocation_tag:0x51a4000000000004};
fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 if bytes.len()!=1880 {return Err(ProgramError::InvalidAccountData);}
 let phase=unsafe{PHASE.value};assert!(phase<2);
 assert_eq!(bytes.as_ptr(),unsafe{PUBLIC_PTR.value},"both prefixes decode the exact original public allocation");
 unsafe{HITS.value[phase]+=1;}
 Err(ProgramError::InvalidAccountData)
}
fn planned_scan(_: &[u8])->bool{false}
#[kani::modifies(unsafe{COUNTERS.value[0].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[1].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[2].cast_mut().cast::<isize>()},
 unsafe{core::ptr::addr_of_mut!(HITS.value)})]
fn native_prefix(program:&Pubkey,accounts:&[AccountInfo<'_>],data:&[u8])->ProgramResult{
 adapter::run(program,accounts,data)
}
#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]
#[kani::stub(crate::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
fn native_owned_decoder_prefix(){
 let program=Pubkey::new_from_array(kani::any());
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);
 let account_count:usize=kani::any();kani::assume(account_count<=3);
 let mut buffers=[Vec::from(kani::any::<[u8;58295]>()),Vec::from(kani::any::<[u8;1880]>()),Vec::from(kani::any::<[u8;1768]>())];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let data_slots:[usize;3]=kani::any();let lamport_slots:[usize;3]=kani::any();
 for i in 0..3 {kani::assume(data_slots[i]<3);kani::assume(lamport_slots[i]<3);}
 let initial_counts:[isize;3]=kani::any();let initial_lamport_counts:[isize;3]=kani::any();
 let rc_counts:[[usize;4];3]=kani::any();
 for i in 0..3 {for j in 0..4 {kani::assume(rc_counts[i][j]>=1);}}
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;
 unsafe{PUBLIC_PTR.value=pointers[1];HITS.value=[0;2];PHASE.value=0;}
 let actual={
 let [ref mut b0,ref mut b1,ref mut b2]=buffers;
 let [ref mut l0,ref mut l1,ref mut l2]=amounts;
 let mut accounts=[
  AccountInfo::new(&keys[0],flags[0][0],flags[0][1],l0,b0,&owners[0],flags[0][2],rents[0]),
  AccountInfo::new(&keys[1],flags[1][0],flags[1][1],l1,b1,&owners[1],flags[1][2],rents[1]),
  AccountInfo::new(&keys[2],flags[2][0],flags[2][1],l2,b2,&owners[2],flags[2][2],rents[2]),
 ];
 let data_roots=[accounts[0].data.clone(),accounts[1].data.clone(),accounts[2].data.clone()];
 let lamport_roots=[accounts[0].lamports.clone(),accounts[1].lamports.clone(),accounts[2].lamports.clone()];
 for i in 0..3 {accounts[i].data=data_roots[data_slots[i]].clone();accounts[i].lamports=lamport_roots[lamport_slots[i]].clone();}
''' + rc + r'''
 let counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&data_roots[i]).cast::<Cell<isize>>());
 let lamport_counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<Cell<isize>>());
 for i in 0..3 {assert_eq!(unsafe{(*counters[i]).get()},0);assert_eq!(unsafe{(*lamport_counters[i]).get()},0);unsafe{(*counters[i]).set(initial_counts[i]);(*lamport_counters[i]).set(initial_lamport_counts[i]);}}
 unsafe{COUNTERS.value=counters;}
 let actual=native_prefix(&program,&accounts[..account_count],&instruction[..instruction_len]);
 assert!(actual.is_err());
 for i in 0..3 {
  assert_eq!(unsafe{(*counters[i]).get()},initial_counts[i]);
  assert_eq!(unsafe{(*lamport_counters[i]).get()},initial_lamport_counts[i]);
  assert_eq!(std::rc::Rc::strong_count(&data_roots[i]),rc_counts[i][0]);
  assert_eq!(std::rc::Rc::weak_count(&data_roots[i]),rc_counts[i][1]-1);
  assert_eq!(std::rc::Rc::strong_count(&lamport_roots[i]),rc_counts[i][2]);
  assert_eq!(std::rc::Rc::weak_count(&lamport_roots[i]),rc_counts[i][3]-1);
 }
 for i in 0..3 {unsafe{
  (*counters[i]).set(0);(*lamport_counters[i]).set(0);
  *data_strong[i]=original_rc[i][0];*data_weak[i]=original_rc[i][1];
  *lamport_strong[i]=original_rc[i][2];*lamport_weak[i]=original_rc[i][3];
 }}
 actual
 };
 assert_eq!(amounts,initial_amounts);
 // Native handles are now gone. The native modifies contract must have proved
 // that no account bytes/Vec descriptor or other external allocation changed.
 if unsafe{HITS.value[0]}==1 {
  let model=OwnedSdk{
   accounts:(0..account_count).map(|i|OwnedAccount{key:keys[i].to_bytes(),owner:owners[i].to_bytes(),is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:data_slots[i],lamports_slot:lamport_slots[i]}).collect(),
   data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:initial_counts[i],strong:rc_counts[i][0],weak:rc_counts[i][1]-1}).collect(),
   lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:initial_amounts[i],borrowed:initial_lamport_counts[i],strong:rc_counts[i][2],weak:rc_counts[i][3]-1}).collect(),
  };
  unsafe{PHASE.value=1;}
  let (expected,model)=owned::owned_stage1(program.to_bytes(),model,instruction[..instruction_len].to_vec());
  assert_eq!(actual,Err(ProgramError::InvalidAccountData));
  assert_eq!(actual,expected,"native reached decoder implies same complete reference decoder/error");
  assert_eq!(unsafe{HITS.value},[1,1]);
  for i in 0..3 {
   assert_eq!(model.data_cells[i].bytes.as_ptr(),pointers[i],"reference preserves the original allocation, not a copied carrier");
   assert_eq!(model.data_cells[i].borrowed,initial_counts[i]);
   assert_eq!(model.data_cells[i].strong,rc_counts[i][0]);assert_eq!(model.data_cells[i].weak,rc_counts[i][1]-1);
   assert_eq!(model.lamports_cells[i].amount,initial_amounts[i]);assert_eq!(model.lamports_cells[i].borrowed,initial_lamport_counts[i]);
   assert_eq!(model.lamports_cells[i].strong,rc_counts[i][2]);assert_eq!(model.lamports_cells[i].weak,rc_counts[i][3]-1);
  }
 }
 kani::cover!(unsafe{HITS.value}==[1,1],"native and complete borrowed reference reach the same original decoder bytes");
 kani::cover!(unsafe{HITS.value}==[1,1]&&initial_counts[0]==isize::MAX,"decoder entry before proof acquisition supports saturated proof borrow");
}
}
'''
unreachable_cuts='unreachable-cuts' in sys.argv[2:]
if unreachable_cuts:
 s=s.replace('fn planned_scan(_: &[u8])->bool{false}', '''fn planned_scan(_: &[u8])->bool{false}
fn unreachable_first(_:Public<'_>,_:&[u8],_:&[u8],_:usize)->Result<Vec<u8>,ProgramError>{panic!("decoder-error prefix must never reach first_decoded")}
fn unreachable_validate(_:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{panic!("decoder-error prefix must never reach validator")}
fn unreachable_encode(_:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{panic!("decoder-error prefix must never reach encoder")}
''')
 s=s.replace('#[kani::stub(crate::decode_public_statement_box,planned_decode)]', '''#[kani::stub(crate::first_decoded,unreachable_first)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::first_decoded,unreachable_first)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,unreachable_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,unreachable_encode)]
#[kani::stub(crate::decode_public_statement_box,planned_decode)]''')
exact_vec='exact-vec' in sys.argv[2:]
if exact_vec:
 for count in [58295,1880,1768]:s=s.replace('Vec::from(kani::any::<[u8;'+str(count)+']>())','kani::vec::exact_vec::<u8,'+str(count)+'>()')
havoc_inputs='havoc-inputs' in sys.argv[2:]
if havoc_inputs:
 s=s.replace('fn planned_scan(_: &[u8])->bool{false}','''#[inline(never)] fn s126_input_bytes(p:*mut u8,n:usize)->usize {let _=(p,n);panic!("input initialization must be linked before verification")}
fn symbolic_buffer<const N:usize>()->Vec<u8>{
 let mut bytes=Box::<[u8;N]>::new_uninit();
 s126_input_bytes(bytes.as_mut_ptr().cast(),N);
 let bytes:Box<[u8]>=unsafe{bytes.assume_init()};bytes.into_vec()
}
fn planned_scan(_: &[u8])->bool{false}''')
 for count in [58295,1880,1768]:s=s.replace('Vec::from(kani::any::<[u8;'+str(count)+']>())','symbolic_buffer::<'+str(count)+'>()')
canonical='canonical-data' in sys.argv[2:]
if canonical:s=s.replace('let data_slots:[usize;3]=kani::any();','let data_slots:[usize;3]=[0,1,2];')
constructor_errors='constructor-errors' in sys.argv[2:]
if constructor_errors:
 before='assert_eq!(actual,Err(ProgramError::InvalidAccountData));'
 assert s.count(before)==1;s=s.replace(before,'assert!(matches!(&actual,Err(ProgramError::InvalidAccountData)));')
 before='assert_eq!(actual,expected,"native reached decoder implies same complete reference decoder/error");'
 assert s.count(before)==1;s=s.replace(before,'assert!(matches!((&actual,&expected),(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))),"native reached decoder implies same complete reference decoder/error");')
(O/'src/lib.rs').write_text(s)
c=(E/'sources/sdk-native-context-v9/Cargo.toml').read_text().replace('name="aspis-s126-sdk-native-context-v1"','name="aspis-s126-sdk-shared-prefix"').replace('aspis-s126-owned-sdk-snapshots={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/owned-sdk-snapshots-v1"}','aspis-s126-owned-sdk-borrowed={path="/home/dombarker/project-offloads/s126-real-sdk-20261021/owned-sdk-borrowed-v1"}')
(O/'Cargo.toml').write_text(c)
sha=lambda b:hashlib.sha256(b).hexdigest()
(O/'source-cut.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',source_sha256=sha(s.encode()),native_source_prefix_sha256=sha(native.encode()),base_source_sha256=sha(base.encode()),borrowed_reference_source_sha256=sha((E/'sources/owned-sdk-borrowed-v1/src/lib.rs').read_bytes()),qualification=__doc__,domain='All proof58295/public1880/checkpoint1768 bytes in original owned allocations, all account metadata, every signed borrow flag, every nonzero usize Rc header, independent arbitrary data/lamport aliases and instruction/account lengths0..3. Native prefix frame forbids all byte/descriptor/metadata writes; only three borrow-counter cells and the decoder-hit array are permitted. After native SDK owners drop, the complete borrowed reference consumes those same original buffers without snapshots. Native decoder entry implies identical reference entry/error and scalar heap restoration.',remaining='Native exact std-any is a separately checked pure overapproximation; reference scan is false in the reached-decoder context and needs concrete source-scan transport. Common decoder returns InvalidAccountData cut; later success continuations, general runtime heap embedding and ordered child/state/log/oracle composition are not proved. Codegen/frame attributes alone are not a frame certificate; raw DFCC enforcement and every reachable property must pass.'),indent=2)+'\n')
if unreachable_cuts:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['unreachable_cuts']='Both native/owned first_decoded and actual validator/encoder receive assert-false panic cuts, not successful replies. Every cut reachability/safety assertion must pass. This removes statically retained verifier/arithmetic bodies from frame instrumentation; it does not assume their unreachability.';p.write_text(json.dumps(m,indent=2)+'\n')
if exact_vec:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['input_constructor']='Pinned Kani library vec::exact_vec<u8,N>: Box::new(any<[u8;N]>()) followed by boxed-slice into_vec; every input byte remains independently arbitrary. No buffer byte is fixed, left uninitialized, or assumed. Native source, model, assertions and enforced write set are unchanged.';p.write_text(json.dumps(m,indent=2)+'\n')
if canonical:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['canonical_input_context']='Data slots are[0,1,2], independently arbitrary lamport aliases remain. The separate unseeded sdk-native-entry-cut-v2 derives this condition for actual proof-prefix comparison entry across every data alias. This focused prefix frame/pair is conditional on that normalized input context; composition from actual accepted execution still must consume both cuts and the exact native guard. No arbitrary-runtime or whole-S2 closure follows.';p.write_text(json.dumps(m,indent=2)+'\n')

if havoc_inputs:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['input_constructor']='Harness-only fresh Box<MaybeUninit<[u8;N]>>, linked CBMC __CPROVER_havoc_slice on the entire byte allocation, then assume_init and boxed-slice into_vec. All bytes arbitrary, no buffer copies or fixed values. The native SDK and complete reference consume the same allocations; intrinsic initialization semantics/exact C implementation are explicit tool trust.';p.write_text(json.dumps(m,indent=2)+'\n')

if constructor_errors:
 p=O/'source-cut.json';m=json.loads(p.read_text());m['error_assertions']='Constructor-complete matches replace derived ProgramError/Result PartialEq/Debug assertions in the proof harness only. Both results must be exactly Err(InvalidAccountData), preserving full status equality at this decoder-error cut; no payload/error/state premise is removed. Frozen SDK/caller and complete reference bodies, input domains and enforced native frame are unchanged.';p.write_text(json.dumps(m,indent=2)+'\n')
