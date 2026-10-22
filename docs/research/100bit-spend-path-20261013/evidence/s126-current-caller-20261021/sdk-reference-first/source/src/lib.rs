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
#[derive(Clone,Copy)] struct Plan {statement:PoolV1PairForestTerminalStatementV1,candidate:[u8;688],output:[u8;1768],k:usize}
static mut PLAN:GhostStorage<Option<Plan>>=GhostStorage{value:None,allocation_tag:5882264063299289091};
static mut PHASE:GhostStorage<usize>=GhostStorage{value:0,allocation_tag:5882264063299289092};
static mut CALLS:GhostStorage<[[u8;4];2]>=GhostStorage{value:[[0;4];2],allocation_tag:5882264063299289093};
static mut NATIVE_ROOT_PTRS:GhostStorage<[*const u8;3]>=GhostStorage{value:[core::ptr::null();3],allocation_tag:5882264063299289094};
static mut MODEL_ROOT_PTRS:GhostStorage<[*const u8;3]>=GhostStorage{value:[core::ptr::null();3],allocation_tag:5882264063299289095};
static mut PUBLIC_SNAPSHOT_PTR:GhostStorage<*const u8>=GhostStorage{value:core::ptr::null(),allocation_tag:5882264063299289096};
static mut PROOF_SNAPSHOT_PTR:GhostStorage<*const u8>=GhostStorage{value:core::ptr::null(),allocation_tag:5882264063299289097};
static mut BOX_PTRS:GhostStorage<[*const PoolV1PairForestTerminalStatementV1;2]>=GhostStorage{value:[core::ptr::null();2],allocation_tag:5882264063299289098};
static mut CANDIDATE_PTRS:GhostStorage<[*const PoolV1PairVerifiedAfterstateV1;2]>=GhostStorage{value:[core::ptr::null();2],allocation_tag:5882264063299289099};
static mut PUBLIC_KIND:GhostStorage<[u8;2]>=GhostStorage{value:[0;2],allocation_tag:5882264063299289100};
static mut PUBLIC_PARTS:GhostStorage<[[*const ();2];2]>=GhostStorage{value:[[core::ptr::null();2];2],allocation_tag:5882264063299289101};
fn plan()->&'static Plan {unsafe{PLAN.value.as_ref().unwrap()}}
fn planned_decode(bytes:&[u8])->Result<Box<PoolV1PairForestTerminalStatementV1>,ProgramError>{
 if bytes.len()!=1880 {return Err(ProgramError::InvalidAccountData);}
 let phase=unsafe{PHASE.value};assert!(phase<2);assert_eq!(unsafe{CALLS.value[phase]},[0,0,0,0]);
 let expected=unsafe{NATIVE_ROOT_PTRS.value[1]};
 assert_eq!(bytes.as_ptr(),expected);
 let boxed=Box::new(plan().statement);
 unsafe{BOX_PTRS.value[phase]=&*boxed;CANDIDATE_PTRS.value[phase]=&boxed.common().lane_transition.candidate_afterstate;CALLS.value[phase][0]+=1;}
 match boxed.semantic_public() {
  Public::Transfer(a,b)=>unsafe{PUBLIC_KIND.value[phase]=0;PUBLIC_PARTS.value[phase]=[a as *const _ as *const (),b as *const _ as *const ()];},
  Public::Withdrawal(a,b)=>unsafe{PUBLIC_KIND.value[phase]=1;PUBLIC_PARTS.value[phase]=[a as *const _ as *const (),b as *const _ as *const ()];},
 }
 Ok(boxed)
}
fn planned_validate(statement:&PoolV1PairForestTerminalStatementV1)->Result<(),PoolV1PairForestTerminalFormatErrorV1>{
 let phase=unsafe{PHASE.value};assert_eq!(unsafe{CALLS.value[phase]},[1,0,0,0]);assert_eq!(statement as *const _,unsafe{BOX_PTRS.value[phase]});unsafe{CALLS.value[phase][1]+=1;}Ok(())
}
fn planned_encode(afterstate:&PoolV1PairVerifiedAfterstateV1)->Result<[u8;688],PoolV1PairVerifierTransportErrorV1>{
 let phase=unsafe{PHASE.value};assert_eq!(unsafe{CALLS.value[phase]},[1,1,0,0]);assert_eq!(afterstate as *const _,unsafe{CANDIDATE_PTRS.value[phase]});unsafe{CALLS.value[phase][2]+=1;}Ok(plan().candidate)
}
fn public_snapshot(bytes:&Vec<u8>)->Vec<u8>{
 assert_eq!(unsafe{PHASE.value},1);assert_eq!(bytes.len(),1880);assert_eq!(bytes.as_ptr(),unsafe{MODEL_ROOT_PTRS.value[1]});
 let output=bytes.clone();unsafe{PUBLIC_SNAPSHOT_PTR.value=output.as_ptr();}output
}
fn proof_snapshot(bytes:&Vec<u8>)->Vec<u8>{
 assert_eq!(unsafe{PHASE.value},1);assert_eq!(bytes.len(),58295);assert_eq!(bytes.as_ptr(),unsafe{MODEL_ROOT_PTRS.value[0]});
 let output=bytes.clone();unsafe{PROOF_SNAPSHOT_PTR.value=output.as_ptr();}output
}
fn planned_zero_scan(_:Vec<u8>)->bool {false}
fn unreachable_error(_:verifier::Error)->ProgramError {assert!(false,"successful verifier reply never calls error mapper");ProgramError::InvalidInstructionData}
fn planned_tx1<H:aspis_core::Digest32>(public:Public<'_>,bytes:&[u8],proof:&[u8],k:usize,_:H,observer:verifier::Observer)->Result<Vec<u8>,verifier::Error>{
 let phase=unsafe{PHASE.value};assert!(phase<2);assert_eq!(unsafe{CALLS.value[phase]},[1,1,1,0]);assert!(observer.is_none());assert_eq!(k,plan().k);
 let expected_public=unsafe{NATIVE_ROOT_PTRS.value[1]};
 let expected_proof=unsafe{NATIVE_ROOT_PTRS.value[0]};
 assert_eq!(bytes.as_ptr(),expected_public);assert_eq!(bytes.len(),1880);
 assert_eq!(proof.as_ptr(),unsafe{expected_proof.add(688)});assert_eq!(proof.len(),57607);
 match public {
  Public::Transfer(a,b)=>{assert_eq!(unsafe{PUBLIC_KIND.value[phase]},0);assert_eq!(a as *const _ as *const (),unsafe{PUBLIC_PARTS.value[phase][0]});assert_eq!(b as *const _ as *const (),unsafe{PUBLIC_PARTS.value[phase][1]});},
  Public::Withdrawal(a,b)=>{assert_eq!(unsafe{PUBLIC_KIND.value[phase]},1);assert_eq!(a as *const _ as *const (),unsafe{PUBLIC_PARTS.value[phase][0]});assert_eq!(b as *const _ as *const (),unsafe{PUBLIC_PARTS.value[phase][1]});},
 }
 unsafe{CALLS.value[phase][3]+=1;}
 Ok(plan().output.to_vec())
}
fn statement()->PoolV1PairForestTerminalStatementV1 {
 let common=aspis_statement::pool_v1::PoolV1PairForestTerminalCommonV1{master_account:core::array::from_fn(|_| kani::any::<u8>()),checkpoint_account:core::array::from_fn(|_| kani::any::<u8>()),selected_lane_account:core::array::from_fn(|_| kani::any::<u8>()),output_lane:kani::any::<u8>(),checkpoint_sequence:kani::any::<u64>(),historical_global_anchor:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),lane_transition:aspis_statement::pool_v1::PoolV1PairLatePublicStatementV1{live_snapshot:aspis_statement::pool_v1::PoolV1PairLiveSnapshotV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),sequence:kani::any::<u64>(),next_pair_index:kani::any::<u64>(),current_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))},candidate_afterstate:aspis_statement::pool_v1::PoolV1PairVerifiedAfterstateV1{next_pair_index:kani::any::<u64>(),next_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),next_frontier:core::array::from_fn(|_| core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())))}}};
 if kani::any::<bool>() {
 PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public:aspis_statement::pool_v1::PoolV1PrivateTransferPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),recipient_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 } else {
 PoolV1PairForestTerminalStatementV1::Withdrawal{common,public:aspis_statement::pool_v1::PoolV1WithdrawalPublicV1{pool:core::array::from_fn(|_| kani::any::<u8>()),deployment_domain:core::array::from_fn(|_| kani::any::<u8>()),anchor_sequence:kani::any::<u64>(),anchor_root:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),nullifier:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>())),asset_id:aspis_core::field::M31(kani::any::<u32>()),amount:kani::any::<u32>(),destination_token_account:core::array::from_fn(|_| kani::any::<u8>()),change_commitment:core::array::from_fn(|_| aspis_core::field::M31(kani::any::<u32>()))}}
 }
}


#[no_mangle] pub static mut s126_keep_coupled_cmp:GhostStorage<Option<extern "C" fn(*const u8,*const u8,usize)->i32>>=GhostStorage{value:None,allocation_tag:0x51a9000000000001};
#[no_mangle] pub extern "C" fn s126_coupled_cmp(a:*const u8,b:*const u8,n:usize)->i32 {
 assert_eq!(n,688);assert_eq!(unsafe{CALLS.value[0]},[1,1,1,0]);
 let root=unsafe{NATIVE_ROOT_PTRS.value[0]};assert!(a==root||b==root);
 0 // Native admitted-gate comparison status; source/value transport required.
}
fn planned_scan(_: &[u8])->bool{false}
fn unreachable_copy<T:Copy>(_:&mut[T],_:&[T]){panic!("empty first reply must reject before checkpoint copy")}

#[kani::proof] #[kani::unwind(700)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::decode_public_statement_box,planned_decode)]
#[kani::stub(aspis_s126_owned_sdk_borrowed::owned_checkpoint_nonzero,planned_scan)]
#[kani::stub(aspis_statement::pool_v1::validate_pool_v1_pair_forest_terminal_statement_v1,planned_validate)]
#[kani::stub(aspis_statement::pool_v1::encode_pool_v1_pair_verified_afterstate_v1,planned_encode)]
#[kani::stub(aspis_r1_cost_probe::verifier::tx1,planned_tx1)]
fn native_owned_decoder_prefix(){
 unsafe{s126_keep_coupled_cmp.value=Some(s126_coupled_cmp);}
 let program:[u8;32]=kani::any();let keys:[[u8;32];3]=kani::any();let owners:[[u8;32];3]=kani::any();
 let flags:[[bool;3];3]=kani::any();let rents:[u64;3]=kani::any();let split:u8=kani::any();
 kani::assume(split==10 || split==11);kani::assume(keys[0]!=keys[1]&&keys[0]!=keys[2]&&keys[1]!=keys[2]);
 kani::assume(!flags[0][0]&&!flags[0][1]&&!flags[0][2]);kani::assume(!flags[1][0]&&!flags[1][1]&&!flags[1][2]);
 kani::assume(owners[2]==program&&!flags[2][0]&&flags[2][1]&&!flags[2][2]);
 let candidate:[u8;688]=kani::any();let output:[u8;1768]=kani::any();
 let mut proof=kani::vec::exact_vec::<u8,58295>();proof[696]=2;
 let buffers=[proof,kani::vec::exact_vec::<u8,1880>(),kani::vec::exact_vec::<u8,1768>()];
 let pointers=core::array::from_fn::<_,3,_>(|i|buffers[i].as_ptr());
 let counts:[isize;3]=kani::any();kani::assume(counts[2]==0);
 for i in 0..2{kani::assume(counts[i]>=0 && counts[i]<isize::MAX);}
 let lamport_slots:[usize;3]=kani::any();for i in 0..3{kani::assume(lamport_slots[i]<3);}
 let lamport_counts:[isize;3]=kani::any();let rc:[[usize;4];3]=kani::any();for i in 0..3{for j in 0..4{kani::assume(rc[i][j]>=1);}}
 let amounts:[u64;3]=kani::any();let index:usize=kani::any();kani::assume(index<1768);
 unsafe{NATIVE_ROOT_PTRS.value=pointers;CALLS.value=[[0;4];2];PHASE.value=0;PLAN.value=Some(Plan{statement:statement(),candidate,output,k:split as usize});}
 let model=OwnedSdk{
 accounts:(0..3).map(|i|OwnedAccount{key:keys[i],owner:owners[i],is_signer:flags[i][0],is_writable:flags[i][1],executable:flags[i][2],rent_epoch:rents[i],data_slot:i,lamports_slot:lamport_slots[i]}).collect(),
 data_cells:buffers.into_iter().enumerate().map(|(i,bytes)|OwnedDataCell{bytes,borrowed:counts[i],strong:rc[i][0],weak:rc[i][1]-1}).collect(),
 lamports_cells:(0..3).map(|i|OwnedLamportsCell{amount:amounts[i],borrowed:lamport_counts[i],strong:rc[i][2],weak:rc[i][3]-1}).collect()};
 let(result,out)=owned::owned_stage1(program,model,vec![3,split]);
 assert!(result.is_ok(),"native-derived first facts construct successful complete borrowed reference");
 assert_eq!(unsafe{CALLS.value[0]},[1,1,1,1]);assert_eq!(out.data_cells[2].bytes[index],output[index]);
 for i in 0..3{
 if i<2{assert_eq!(out.data_cells[i].bytes.as_ptr(),pointers[i]);}assert_eq!(out.data_cells[i].borrowed,counts[i]);
 assert_eq!(out.data_cells[i].strong,rc[i][0]);assert_eq!(out.data_cells[i].weak,rc[i][1]-1);
 assert_eq!(out.lamports_cells[i].amount,amounts[i]);assert_eq!(out.lamports_cells[i].borrowed,lamport_counts[i]);
 assert_eq!(out.lamports_cells[i].strong,rc[i][2]);assert_eq!(out.lamports_cells[i].weak,rc[i][3]-1);}
 kani::cover!(result.is_ok()&&counts[0]==isize::MAX-1,"successful reference with maximum permitted proof count");
 kani::cover!(result.is_ok()&&split==11,"successful reference split11");
}
}
