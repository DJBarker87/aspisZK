#![allow(dead_code,unexpected_cfgs)]
use aspis_r1_cost_probe::{verifier,transport::Variant};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalStatementV1,POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES,decode_pool_v1_pair_forest_terminal_statement_v1,validate_pool_v1_pair_forest_terminal_statement_v1,encode_pool_v1_pair_verified_afterstate_v1};
use solana_program::{program_error::ProgramError,entrypoint::ProgramResult,hash::hashv,msg};
#[derive(Clone,Copy)] struct SolanaDigest;
impl aspis_core::Digest32 for SolanaDigest {
 fn digest(&self,parts:&[&[u8]])->[u8;32] {hashv(parts).to_bytes()}
}
// The exact cfg-off observer body. Error logging remains a distinct child.
fn observer()->verifier::Observer {None}
fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}
fn first_decoded(public:aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public<'_>,public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    verifier::tx1(public,public_bytes,proof,k,SolanaDigest,observer()).map_err(error)
}
fn decode_public_statement_box(
    bytes: &[u8],
) -> Result<Box<PoolV1PairForestTerminalStatementV1>, ProgramError> {
    Ok(Box::new(
        decode_pool_v1_pair_forest_terminal_statement_v1(bytes)
            .map_err(|_| ProgramError::InvalidAccountData)?,
    ))
}


use solana_program::{account_info::AccountInfo,pubkey::Pubkey};
use aspis_statement::pool_v1::{PoolV1PairForestTerminalCommonV1,PoolV1PrivateTransferPublicV1,PoolV1WithdrawalPublicV1,PoolV1PairVerifiedAfterstateV1,PoolV1PairForestTerminalFormatErrorV1,PoolV1PairVerifierTransportErrorV1};
use aspis_statement::pool_v1::pair_forest_semantic_terminal::r0::Public;
mod adapter {use super::*;
fn readonly_buffer_meta_ok(
    is_signer: bool,
    is_writable: bool,
    executable: bool,
) -> ProgramResult {
    if is_signer || is_writable || executable {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_readonly_buffer(account: &AccountInfo<'_>) -> ProgramResult {
    readonly_buffer_meta_ok(account.is_signer, account.is_writable, account.executable)
}
fn require_verifier_checkpoint(
    account: &AccountInfo<'_>,
    program_id: &Pubkey,
    writable: bool,
) -> ProgramResult {
    if account.owner != program_id || account.is_signer || account.executable
        || account.is_writable != writable
        || account.try_data_len()? != verifier::checkpoint_size(Variant::S2)
    {
        return Err(ProgramError::InvalidAccountData);
    }
    Ok(())
}
fn require_distinct_accounts<const N: usize>(accounts: &[&AccountInfo<'_>; N]) -> ProgramResult {
    for (index, account) in accounts.iter().enumerate() {
        if accounts[..index]
            .iter()
            .any(|previous| previous.key == account.key)
        {
            return Err(ProgramError::InvalidArgument);
        }
    }
    Ok(())
}
fn stage1(program_id: &Pubkey, accounts: &[AccountInfo<'_>], data: &[u8]) -> ProgramResult {
    if !(data == &[3, 10] || data == &[3, 11]) || accounts.len() != 3 {
        return Err(ProgramError::InvalidInstructionData);
    }
    let proof_account = &accounts[0];
    let public_account = &accounts[1];
    let checkpoint_account = &accounts[2];
    require_distinct_accounts(&[proof_account, public_account, checkpoint_account])?;
    require_readonly_buffer(proof_account)?;
    require_readonly_buffer(public_account)?;
    require_verifier_checkpoint(checkpoint_account, program_id, true)?;
    let mut checkpoint_data = checkpoint_account.try_borrow_mut_data()?;
    if checkpoint_data.iter().any(|byte| *byte != 0) {
        return Err(ProgramError::AccountAlreadyInitialized);
    }
    let public_data = public_account.try_borrow_data()?;
    let statement = decode_public_statement_box(&public_data)?;
    validate_pool_v1_pair_forest_terminal_statement_v1(&statement)
        .map_err(|_| ProgramError::InvalidAccountData)?;
    let candidate = encode_pool_v1_pair_verified_afterstate_v1(
        &statement.common().lane_transition.candidate_afterstate,
    )
    .map_err(|_| ProgramError::InvalidAccountData)?;

    let proof_data = proof_account.try_borrow_data()?;
    let proof_length = verifier::PROOF_BYTES;
    let proof_start = POOL_V1_PAIR_VERIFIED_AFTERSTATE_BYTES;
    let proof_end = proof_start.checked_add(proof_length)
        .ok_or(ProgramError::InvalidAccountData)?;
    if proof_data.len() != proof_end
        || proof_data[..proof_start] != candidate
        || proof_data[proof_start + 8] != Variant::S2.tag()
    {
        return Err(ProgramError::InvalidAccountData);
    }
    let checkpoint = super::first_decoded(statement.semantic_public(), &public_data, &proof_data[proof_start..proof_end], data[1] as usize)?;
    if checkpoint.len() != checkpoint_data.len() {
        return Err(ProgramError::InvalidAccountData);
    }
    checkpoint_data.copy_from_slice(&checkpoint);
    #[cfg(feature="cu-profiling")]
    {
    msg!("r1:pool-adapter-stage1-checkpoint-written");
    solana_program::log::sol_log_compute_units();
    }
    Ok(())
}
pub fn run(program:&Pubkey,accounts:&[AccountInfo<'_>],data:&[u8])->ProgramResult {stage1(program,accounts,data)}
}
#[cfg(kani)] mod proofs {
use super::*;
 static mut OBSERVED:usize=0;
 static mut EXPECTED:u8=0;
 fn observed()->usize {unsafe{OBSERVED}}
 fn expected()->u8 {unsafe{EXPECTED}}
 #[kani::requires(destination.len()==1768 && source.len()==1768)]
 #[kani::requires(observed()<1768)]
 #[kani::requires(expected()==source[observed()])]
 #[kani::modifies(destination.as_mut_ptr().cast::<[u8;1768]>())]
 #[kani::ensures(|_| destination[observed()]==expected())]
 fn verified_byte_copy(destination:&mut [u8],source:&[u8]) {
  destination.copy_from_slice(source);
 }
 fn copy_bridge<T:Copy>(destination:&mut [T],source:&[T]) {
  assert_eq!(core::any::type_name::<T>(),"u8","only the actual byte instance is certified");
  assert_eq!(core::mem::size_of::<T>(),1);assert_eq!(core::mem::align_of::<T>(),1);
  let destination=unsafe{core::slice::from_raw_parts_mut(destination.as_mut_ptr().cast::<u8>(),destination.len())};
  let source=unsafe{core::slice::from_raw_parts(source.as_ptr().cast::<u8>(),source.len())};
  verified_byte_copy(destination,source);
 }

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
fn unreachable_error(_:verifier::Error)->ProgramError {assert!(false,"successful verifier reply never calls error mapper");ProgramError::InvalidInstructionData}
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
fn statement()->PoolV1PairForestTerminalStatementV1 {
 let common=aspis_statement::pool_v1::PoolV1PairForestTerminalCommonV1{master_account:core::array::from_fn(|_| kani::any::<u8>()),checkpoint_account:core::array::from_fn(|_| kani::any::<u8>()),selected_lane_account:core::array::from_fn(|_| kani::any::<u8>()),output_lane:kani::any::<u8>(),checkpoint_sequence:kani::any::<u64>(),historical_global_anchor:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),lane_transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1{live_snapshot:aspis_statement::pool_v1::PoolV1PairLiveSnapshotV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),sequence:kani::any::<u64>(),next_pair_index:kani::any::<u64>(),current_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))},candidate_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any::<u64>(),next_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),next_frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))}}};
 if kani::any::<bool>() {
 PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),recipient_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 } else {
 PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:aspis_statement::pool_v1::PoolV1WithdrawalPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),amount:kani::any::<u32>(),destination_token_account:core::array::from_fn(|_| kani::any::<u8>()),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 }
}

#[kani::stub(crate::error,unreachable_error)]
#[kani::stub(aspis_s126_owned_sdk_snapshots::error,unreachable_error)]
#[kani::stub(<[u8]>::copy_from_slice,copy_bridge)]
#[kani::stub_verified(verified_byte_copy)]
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
 let output_len=1768usize;
 unsafe{PLAN=Some(Plan{statement:statement(),candidate:kani::any(),output:kani::any(),output_len,k:instruction[1] as usize});}
 let mut b0:[u8;58295]=kani::any();let mut b1:[u8;1880]=kani::any();let mut b2:[u8;1768]=kani::any();
 unsafe{core::ptr::copy_nonoverlapping(plan().candidate.as_ptr(),b0.as_mut_ptr(),688);}b0[696]=2;
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
 let observed:usize=kani::any();kani::assume(observed<1768);
 unsafe{OBSERVED=observed;EXPECTED=plan().output[observed];PHASE=0;CALLS=[[0;4];2];}
 let actual=adapter::run(&program,&accounts,&instruction[..instruction_len]);
 if actual.is_ok() {
  // Explicit accepted context: pure child replies are common typed values.
  unsafe{PHASE=1;}
  let (expected,model)=aspis_s126_owned_sdk_snapshots::owned_stage1(program.to_bytes(),model,instruction[..instruction_len].to_vec());
  assert!(expected.is_ok());
  for phase in 0..2 {for event in 0..4 {assert_eq!(unsafe{CALLS[phase][event]},1);}}
  assert_eq!(plan().output_len,1768);
  assert_eq!(data_slots,[0,1,2]);
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
