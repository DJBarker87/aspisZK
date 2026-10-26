use solana_program::{account_info::AccountInfo,program_error::ProgramError,pubkey::Pubkey};
use aspis_statement::pool_v1::*;
// Strict shared-read source cut from F439-440, then the Box constructor used by F704.
// Metadata, self-identity and PDA checks are explicitly excluded from this cut.
fn PoolS2_master_snapshot(account:&AccountInfo<'_>)->Result<Box<PoolV1PairForestMasterV1>,ProgramError>{
 let master=decode_pool_v1_pair_forest_master_v1(&account.try_borrow_data()?).map_err(|_|ProgramError::Custom(0x41532001))?;
 Ok(Box::new(master))
}
#[cfg(kani)] mod PoolS2_checks{use super::*;
#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_snapshot_bump(){
 let initial:[u8;384]=kani::any();let mut data=initial;let mut funds:u64=kani::any();
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let flags:[bool;3]=kani::any();
 let account=AccountInfo::new(&key,flags[0],flags[1],&mut funds,&mut data,&owner,flags[2],0);
 if let Ok(master)=PoolS2_master_snapshot(&account){assert!(master.bump==initial[7]);}
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_snapshot_frame(){
 let initial:[u8;384]=kani::any();let mut data=initial;let mut funds:u64=kani::any();
 let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let flags:[bool;3]=kani::any();
 let account=AccountInfo::new(&key,flags[0],flags[1],&mut funds,&mut data,&owner,flags[2],0);
 let _reply=PoolS2_master_snapshot(&account);
 let j:usize=kani::any();kani::assume(j<384);
 assert!(account.try_borrow_mut_data().unwrap()[j]==initial[j]);
}
#[kani::proof]
#[kani::unwind(195)]
fn PoolS2_checkpoint_signing_seeds(){
 let image:[u8;192]=kani::any();let master=Pubkey::new_from_array(kani::any());
 if let Ok(checkpoint_state)=decode_pool_v1_pair_forest_checkpoint_v1(&image){
 let sequence_bytes=checkpoint_state.checkpoint_sequence.to_le_bytes();
 let bump_bytes=[checkpoint_state.bump];
 let seeds:&[&[u8]]=&[b"aspis-pair-forest-checkpoint-v1",master.as_ref(),&sequence_bytes,&bump_bytes];
 let expected:&[&[u8]]=&[b"aspis-pair-forest-checkpoint-v1",master.as_ref(),&image[72..80],&image[7..8]];
 assert!(seeds==expected);
 }
}

}
