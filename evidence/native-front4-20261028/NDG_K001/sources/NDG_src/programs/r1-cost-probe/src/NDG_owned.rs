use super::*;
fn arbitrary_account()->OwnedAccount {
 OwnedAccount {key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::InvalidAccountData)}
}
#[kani::proof_for_contract(OwnedAccount::owner)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(34)]
fn owner_contract(){let a=arbitrary_account();let _=a.owner();}
#[kani::proof_for_contract(OwnedAccount::key)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NDG_kmx::KMX_copy_nonoverlapping)]
#[kani::unwind(34)]
fn key_contract(){let a=arbitrary_account();let _=a.key();}
