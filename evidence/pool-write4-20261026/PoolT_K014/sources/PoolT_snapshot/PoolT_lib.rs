use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
const POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES:usize=768;
fn stored_lane_bump(account: &AccountInfo<'_>) -> Result<Option<u8>, ProgramError> {
    let data = account.try_borrow_data()?;
    Ok((data.len() == POOL_V1_PAIR_FOREST_LANE_ACCOUNT_BYTES).then(|| data[72]))
}

#[cfg(kani)] mod PoolT_checks{
use super::*;
#[kani::proof]
#[kani::unwind(80)]
fn PoolT_stored_lane_snapshot(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut bytes:[u8;768]=kani::any();let bump=bytes[72];
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());
 assert!(stored_lane_bump(&a)==Ok(Some(bump)));
 assert!(a.data.try_borrow_mut().is_ok());assert!(a.try_borrow_data().unwrap()[72]==bump);
}
#[kani::proof]
#[kani::unwind(80)]
fn PoolT_stored_lane_conflict(){
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
 let mut lamports:u64=kani::any();let mut bytes:[u8;768]=kani::any();
 let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());
 let held=a.try_borrow_mut_data().unwrap();
 assert!(stored_lane_bump(&a)==Err(ProgramError::AccountBorrowFailed));
 drop(held);assert!(a.try_borrow_mut_data().is_ok());
}
}
