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
fn unreachable_first(_:Public<'_>,_:&[u8],_:&[u8],_:usize)->Result<Vec<u8>,ProgramError>{panic!("decoder-error prefix must never reach first_decoded")}
fn unreachable_validate(_:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{panic!("decoder-error prefix must never reach validator")}
fn unreachable_encode(_:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{panic!("decoder-error prefix must never reach encoder")}

#[kani::modifies(unsafe{COUNTERS.value[0].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[1].cast_mut().cast::<isize>()},
 unsafe{COUNTERS.value[2].cast_mut().cast::<isize>()},
 unsafe{core::ptr::addr_of_mut!(HITS.value)})]
fn native_prefix(program:&Pubkey,accounts:&[AccountInfo<'_>],data:&[u8])->ProgramResult{
 adapter::run(program,accounts,data)
}
#[kani::proof_for_contract(native_prefix)] #[kani::unwind(48)]
#[kani::stub_verified(AccountInfo::try_data_len)]
#[kani::stub_verified(AccountInfo::try_borrow_data)]
#[kani::stub_verified(AccountInfo::try_borrow_mut_data)]

#[kani::stub(crate::first_decoded,unreachable_first)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::first_decoded,unreachable_first)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,unreachable_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,unreachable_encode)]
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
 let mut buffers=[kani::vec::exact_vec::<u8,58295>(),kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
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
