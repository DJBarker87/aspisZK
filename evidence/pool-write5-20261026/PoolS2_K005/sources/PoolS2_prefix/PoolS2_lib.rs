use solana_program::{account_info::AccountInfo,entrypoint::ProgramResult,program_error::ProgramError,pubkey::Pubkey};
pub(crate) fn require_unique_accounts(accounts: &[AccountInfo<'_>]) -> ProgramResult {
    for left in 0..accounts.len() {
        for right in left + 1..accounts.len() {
            if accounts[left].key == accounts[right].key {
                return Err(ProgramError::InvalidArgument);
            }
        }
    }
    Ok(())
}

#[cfg(kani)] mod PoolS2_checks{use super::*;
#[kani::proof]
#[kani::unwind(80)]
fn PoolS2_unique_projection(){
 let keys_bytes:[[u8;32];12]=kani::any();let keys=keys_bytes.map(Pubkey::new_from_array);
 let owner=Pubkey::new_from_array(kani::any());let flags:[[bool;3];12]=kani::any();
 let mut lamports:[u64;12]=kani::any();let mut data:[[u8;1];12]=kani::any();
 let accounts:Vec<_>=keys.iter().zip(lamports.iter_mut()).zip(data.iter_mut()).enumerate().map(|(i,((key,lamports),data))|AccountInfo::new(key,flags[i][0],flags[i][1],lamports,data,&owner,flags[i][2],0)).collect();
 assert!(require_unique_accounts(&accounts).is_ok()==pools2_ref::unique_keys(&keys_bytes));
}
}
