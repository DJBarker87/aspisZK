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

fn native_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,checkpoint:&Vec<u8>,observed:usize,destination:*mut [u8;1768],source:*const [u8;1768],expected:u8)->Result<(),ProgramError> {
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
#[cfg_attr(kani,kani::requires(checkpoint_data.len()==1768 && checkpoint.len()<=1769))]
#[cfg_attr(kani,kani::requires(observed<1768))]
#[cfg_attr(kani,kani::requires(destination==checkpoint_data.as_mut_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::requires(source==checkpoint.as_ptr().cast::<[u8;1768]>()))]
#[cfg_attr(kani,kani::requires(expected==(if checkpoint.len()==1768 {checkpoint[observed]} else {checkpoint_data[observed]})))]
#[cfg_attr(kani,kani::modifies(destination))]
#[cfg_attr(kani,kani::ensures(|result:&bool| *result==(checkpoint.len()==1768) && checkpoint_data[observed]==expected))]
fn encoded_finish(checkpoint_data:&mut std::cell::RefMut<'_,&mut [u8]>,checkpoint:&Vec<u8>,observed:usize,destination:*mut [u8;1768],source:*const [u8;1768],expected:u8)->bool {
 match native_finish(checkpoint_data,checkpoint,observed,destination,source,expected) {
  Ok(())=>true,
  Err(ProgramError::InvalidAccountData)=>false,
  Err(_)=>panic!("frozen finish returned an unrepresented SDK error"),
 }
}

#[cfg(kani)] mod copy_certificate {
 use super::*;
 #[kani::proof_for_contract(encoded_finish)] #[kani::unwind(1772)]
 fn exact_finish_fixed_frame() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let flags:[bool;3]=kani::any();let rent:u64=kani::any();let mut amount:u64=kani::any();
  let mut bytes:[u8;1768]=kani::any();let reply:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let checkpoint=reply[..reply_len].to_vec();
  let observed:usize=kani::any();kani::assume(observed<1768);
  let account=AccountInfo::new(&key,flags[0],flags[1],&mut amount,&mut bytes,&owner,flags[2],rent);
  let mut guard=account.try_borrow_mut_data().unwrap();
  let destination=guard.as_mut_ptr().cast::<[u8;1768]>();let source=checkpoint.as_ptr().cast::<[u8;1768]>();
  let expected=if checkpoint.len()==1768 {checkpoint[observed]} else {guard[observed]};
  let result=encoded_finish(&mut guard,&checkpoint,observed,destination,source,expected);
  kani::cover!(!result,"native whole-copy length rejection preserves observed byte");
  kani::cover!(result&&observed==0,"fixed-size native whole copy first byte");
  kani::cover!(result&&observed==1767,"fixed-size native whole copy last byte");
 }
}
#[cfg(kani)] mod proofs {
use super::*;use std::cell::Cell;
fn statement()->PoolV1PairForestTerminalStatementV1 {
 let common=aspis_statement::pool_v1::PoolV1PairForestTerminalCommonV1{master_account:core::array::from_fn(|_| kani::any::<u8>()),checkpoint_account:core::array::from_fn(|_| kani::any::<u8>()),selected_lane_account:core::array::from_fn(|_| kani::any::<u8>()),output_lane:kani::any::<u8>(),checkpoint_sequence:kani::any::<u64>(),historical_global_anchor:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),lane_transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1{live_snapshot:aspis_statement::pool_v1::PoolV1PairLiveSnapshotV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),sequence:kani::any::<u64>(),next_pair_index:kani::any::<u64>(),current_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))},candidate_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any::<u64>(),next_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),next_frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))}}};
 if kani::any::<bool>() {
 PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),recipient_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 } else {
 PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:aspis_statement::pool_v1::PoolV1WithdrawalPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),amount:kani::any::<u32>(),destination_token_account:core::array::from_fn(|_| kani::any::<u8>()),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 }
}


#[kani::proof] #[kani::unwind(1772)]
#[kani::stub_verified(encoded_finish)]
fn native_post_first_tail(){
 let program=Pubkey::new_from_array(kani::any());
 let keys:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let owners:[Pubkey;3]=core::array::from_fn(|_|Pubkey::new_from_array(kani::any()));
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();
 let instruction:[u8;3]=kani::any();let instruction_len:usize=kani::any();kani::assume(instruction_len<=3);
 let account_count:usize=kani::any();kani::assume(account_count<=3);
 let mut buffers=[kani::vec::exact_vec::<u8,58295>(),kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let selected_root:usize=2;
 let selected_index:usize=kani::any();kani::assume(selected_index<buffers[selected_root].len());
 let lengths=core::array::from_fn::<_,3,_>(|i|buffers[i].len());
 let capacities=core::array::from_fn::<_,3,_>(|i|buffers[i].capacity());
 let initial_byte=buffers[selected_root][selected_index];

 let data_slots:[usize;3]=[0,1,2];let lamport_slots:[usize;3]=kani::any();
 for i in 0..3 {kani::assume(data_slots[i]<3);kani::assume(lamport_slots[i]<3);}
 let initial_counts:[isize;3]=kani::any();let initial_lamport_counts:[isize;3]=kani::any();
 kani::assume(initial_counts[2]==0);
 for i in 0..2 {kani::assume(initial_counts[i]>=0 && initial_counts[i]<isize::MAX);}

 let rc_counts:[[usize;4];3]=kani::any();
 for i in 0..3 {for j in 0..4 {kani::assume(rc_counts[i][j]>=1);}}
 let mut amounts:[u64;3]=kani::any();let initial_amounts=amounts;
 let reply:[u8;1769]=kani::any();let reply_len:usize=kani::any();kani::assume(reply_len<=1769);let first_ok:bool=kani::any();
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
 // Reuse the pinned RcInner layout from the wider primitive certificates.
 let data_strong=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&data_roots[i]).cast::<usize>().sub(2).cast_mut()});
 let data_weak=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&data_roots[i]).cast::<usize>().sub(1).cast_mut()});
 let lamport_strong=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<usize>().sub(2).cast_mut()});
 let lamport_weak=core::array::from_fn::<_,3,_>(|i|unsafe{std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<usize>().sub(1).cast_mut()});
 let original_rc=core::array::from_fn::<_,3,_>(|i|unsafe{[*data_strong[i],*data_weak[i],*lamport_strong[i],*lamport_weak[i]]});
 for i in 0..3 {
  assert_eq!(original_rc[i][0],std::rc::Rc::strong_count(&data_roots[i]));
  assert_eq!(original_rc[i][1],std::rc::Rc::weak_count(&data_roots[i])+1);
  assert_eq!(original_rc[i][2],std::rc::Rc::strong_count(&lamport_roots[i]));
  assert_eq!(original_rc[i][3],std::rc::Rc::weak_count(&lamport_roots[i])+1);
 }
 for i in 0..3 {
  unsafe{*data_strong[i]=rc_counts[i][0];*data_weak[i]=rc_counts[i][1];*lamport_strong[i]=rc_counts[i][2];*lamport_weak[i]=rc_counts[i][3];}
  assert_eq!(std::rc::Rc::strong_count(&data_roots[i]),rc_counts[i][0]);
  assert_eq!(std::rc::Rc::weak_count(&data_roots[i]),rc_counts[i][1]-1);
  assert_eq!(std::rc::Rc::strong_count(&lamport_roots[i]),rc_counts[i][2]);
  assert_eq!(std::rc::Rc::weak_count(&lamport_roots[i]),rc_counts[i][3]-1);
 }

 let counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&data_roots[i]).cast::<Cell<isize>>());
 let lamport_counters=core::array::from_fn::<_,3,_>(|i|std::rc::Rc::as_ptr(&lamport_roots[i]).cast::<Cell<isize>>());
 for i in 0..3 {assert_eq!(unsafe{(*counters[i]).get()},0);assert_eq!(unsafe{(*lamport_counters[i]).get()},0);unsafe{(*counters[i]).set(initial_counts[i]);(*lamport_counters[i]).set(initial_lamport_counts[i]);}}
 let actual={
  let mut checkpoint_data=accounts[2].try_borrow_mut_data().unwrap();
  let public_data=accounts[1].try_borrow_data().unwrap();
  let statement=Box::new(statement());
  let candidate:[u8;688]=kani::any();
  let proof_data=accounts[0].try_borrow_data().unwrap();
  assert_eq!(std::mem::size_of_val(&checkpoint_data),2*std::mem::size_of::<usize>());
  assert_eq!(std::mem::size_of_val(&public_data),2*std::mem::size_of::<usize>());
  assert_eq!(std::mem::size_of_val(&proof_data),2*std::mem::size_of::<usize>());
  assert_eq!(unsafe{*(std::ptr::addr_of!(checkpoint_data).cast::<usize>().add(1))},counters[2] as usize);
  assert_eq!(unsafe{*(std::ptr::addr_of!(public_data).cast::<usize>().add(1))},counters[1] as usize);
  assert_eq!(unsafe{*(std::ptr::addr_of!(proof_data).cast::<usize>().add(1))},counters[0] as usize);
  assert_eq!(checkpoint_data.as_mut_ptr(),pointers[2].cast_mut());
  assert_eq!(public_data.as_ptr(),pointers[1]);assert_eq!(proof_data.as_ptr(),pointers[0]);
  assert_eq!(unsafe{(*counters[2]).get()},-1);
  assert_eq!(unsafe{(*counters[1]).get()},initial_counts[1]+1);
  assert_eq!(unsafe{(*counters[0]).get()},initial_counts[0]+1);
  for c in 0..3 {for d in 0..3 {
   let counter=counters[c] as usize;let start=pointers[d] as usize;
   assert!(counter.checked_add(std::mem::size_of::<isize>()).is_some());
   assert!(start.checked_add(lengths[d]).is_some());
   assert!(counter+std::mem::size_of::<isize>()<=start || start+lengths[d]<=counter,
    "actual guard counter region is disjoint from every account data buffer");
  }}
  let mapped_reply=if first_ok {Ok(reply[..reply_len].to_vec())}else{Err(ProgramError::InvalidInstructionData)};
  let result=(||{
   let checkpoint=mapped_reply?;
   let observed=if selected_root==2 {selected_index}else{0};
   let destination=checkpoint_data.as_mut_ptr().cast::<[u8;1768]>();
   let source=checkpoint.as_ptr().cast::<[u8;1768]>();
   assert_eq!(destination,pointers[2].cast_mut().cast::<[u8;1768]>(),"verified finish frame targets original checkpoint account2 allocation");
   let expected=if checkpoint.len()==1768 {checkpoint[observed]}else{checkpoint_data[observed]};
   let ok=encoded_finish(&mut checkpoint_data,&checkpoint,observed,destination,source,expected);
   if ok {Ok(())} else {Err(ProgramError::InvalidAccountData)}
  })();
  assert_eq!(unsafe{(*counters[2]).get()},-1,"exclusive Drop precondition survives the exact native finish");
  assert!(unsafe{(*counters[1]).get()}>0 && unsafe{(*counters[0]).get()}>0,"both shared Drop preconditions survive finish");
  // Exact relative guard/owner declaration order retained: reply, proof,
  // candidate, actual statement Box, public guard, checkpoint guard.
  let _=(&proof_data,&candidate,&statement,&public_data);
  result
 };
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
 for i in 0..3{assert_eq!(buffers[i].as_ptr(),pointers[i]);assert_eq!(buffers[i].len(),lengths[i]);assert_eq!(buffers[i].capacity(),capacities[i]);}

 if first_ok && reply_len==1768 {
  assert!(actual.is_ok());
  if selected_root==2 {assert_eq!(buffers[2][selected_index],reply[selected_index]);}
  else {assert_eq!(buffers[selected_root][selected_index],initial_byte);}
 } else {
  if first_ok {assert!(matches!(actual,Err(ProgramError::InvalidAccountData)));}
  else {assert!(matches!(actual,Err(ProgramError::InvalidInstructionData)));}
  assert_eq!(buffers[selected_root][selected_index],initial_byte);
 }
 kani::cover!(actual.is_ok()&&selected_root==2&&initial_counts[0]==isize::MAX-1,"native tail saved byte and restored maximum proof borrow count");
 kani::cover!(first_ok&&reply_len!=1768&&matches!(actual,Err(ProgramError::InvalidAccountData)),"native tail exact length error");
 kani::cover!(!first_ok&&matches!(actual,Err(ProgramError::InvalidInstructionData)),"native tail exact mapped first error");
}
}
