//! UNPROVED R1 COST PROBE. Local measurement entrypoint only.
use aspis_r1_cost_probe::verifier::{self,Phase};
use aspis_statement::pool_v1::{decode_pool_v1_pair_forest_terminal_statement_v1,PoolV1PairForestTerminalStatementV1,pair_forest_semantic_terminal::r0::Public};
use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,pubkey::Pubkey,program_error::ProgramError,hash::hashv,msg,log::sol_log_compute_units};
#[cfg(target_os="solana")]
#[global_allocator]
static ALLOCATOR:solana_program::entrypoint::BumpAllocator=solana_program::entrypoint::BumpAllocator{start:solana_program::entrypoint::HEAP_START_ADDRESS as usize,len:256*1024};
#[cfg(not(feature="no-entrypoint"))]
solana_program::entrypoint!(process_r1_cost_probe_instruction);
#[inline(never)]
fn mark(phase:Phase){
    match phase {
        Phase::QueryPart(i,j)=>msg!("r1:query-part:{}:{}",i,j),
        Phase::SemanticPart(i)=>msg!("r1:semantic-part:{}",i),
        Phase::Parsed=>msg!("r1:parsed"),Phase::Semantic=>msg!("r1:semantic"),Phase::Prepare=>msg!("r1:prepare"),
        Phase::CheckpointRead=>msg!("r1:checkpoint-read"),Phase::CheckpointWrite=>msg!("r1:checkpoint-write"),
        Phase::Merkle(i)=>msg!("r1:merkle:{}",i),Phase::Query(i)=>msg!("r1:query:{}",i),
        Phase::Relation=>msg!("r1:relation"),Phase::Final=>msg!("r1:final"),
    }
    sol_log_compute_units();
}
fn error(e:verifier::Error)->ProgramError{msg!("r1:error:{:?}",e);ProgramError::InvalidInstructionData}
#[inline(never)]
fn first(public_bytes:&[u8],proof:&[u8],k:usize)->Result<Vec<u8>,ProgramError>{
    let statement=decode_pool_v1_pair_forest_terminal_statement_v1(public_bytes).map_err(|_|ProgramError::InvalidAccountData)?;
    let public=match &statement{PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}=>Public::Transfer(public,&common.lane_transition),PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}=>Public::Withdrawal(public,&common.lane_transition)};
    verifier::tx1(public,public_bytes,proof,k,|p|hashv(p).to_bytes(),Some(mark)).map_err(error)
}
#[cfg(feature="pool-adapter")]
mod r1_pool_adapter;
pub fn process_r1_cost_probe_instruction(program_id:&Pubkey,accounts:&[AccountInfo],data:&[u8])->ProgramResult{
    #[cfg(feature="pool-adapter")]
    if matches!(data.first().copied(), Some(4 | 5 | 6)) || data == &[3,10] || data.starts_with(b"ASQ8") {
        return r1_pool_adapter::process(program_id,accounts,data);
    }
    if accounts.len()!=3||!matches!(data,[1,0..=22]|[2]) {return Err(ProgramError::InvalidInstructionData);}
    for (i,a) in accounts.iter().enumerate(){if a.owner!=program_id||a.executable||a.is_writable!=(i==2){return Err(ProgramError::InvalidAccountData);}}
    let proof=accounts[0].try_borrow_data()?;let public=accounts[1].try_borrow_data()?;let mut checkpoint=accounts[2].try_borrow_mut_data()?;
    msg!("UNPROVED R1 COST PROBE");msg!("r1:begin");sol_log_compute_units();
    if data[0]==1 {
        if checkpoint.iter().any(|&b|b!=0){return Err(ProgramError::AccountAlreadyInitialized);}
        let bytes=first(&public,&proof,data[1]as usize)?;
        if checkpoint.len()!=bytes.len(){return Err(ProgramError::InvalidAccountData);}
        checkpoint.copy_from_slice(&bytes);
    } else {
        verifier::tx2(&public,&proof,&checkpoint,|p|hashv(p).to_bytes(),Some(mark)).map_err(error)?;
        checkpoint[10]=2;let end=checkpoint.len()-32;let sum=hashv(&[b"UNPROVED:R1:checkpoint",&checkpoint[..end]]).to_bytes();checkpoint[end..].copy_from_slice(&sum);
    }
    msg!("r1:account-write");sol_log_compute_units();
    #[cfg(target_os="solana")]
    unsafe {
        let cursor=*(solana_program::entrypoint::HEAP_START_ADDRESS as *const usize);
        msg!("r1:heap-high-water");solana_program::log::sol_log_64((solana_program::entrypoint::HEAP_START_ADDRESS as usize+256*1024-cursor+core::mem::size_of::<usize>())as u64,0,0,0,0);
    }
    Ok(())
}
