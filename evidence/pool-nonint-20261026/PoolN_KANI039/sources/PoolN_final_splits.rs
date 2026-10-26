#[cfg(kani)]
mod PoolN_final_splits {
 use super::*;
 fn post_create(prep:FreshPdaPreparationV1) {
  let id=Pubkey::new_from_array([7;32]);let foreign=Pubkey::new_from_array([6;32]);let key=Pubkey::new_from_array([8;32]);
  let mut bytes:[u8;1768]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let initial_balance=balance;
  let account=AccountInfo::new(&key,false,true,&mut balance,&mut bytes,&foreign,false,0);
  assert_eq!(require_fresh_rent_exempt_program_pda(&account,&id,&key,384,prep,&Rent::default()),Err(PoolV1ProgramError::InvalidFreshAccount.into()));
  drop(account);assert_eq!(bytes[0],before);assert_eq!(balance,initial_balance);
 }
 #[kani::proof]
 #[kani::unwind(1772)]
 fn PoolN_postcreate_split_program() {post_create(FreshPdaPreparationV1::ProgramOwnedZeroed)}
 #[kani::proof]
 #[kani::unwind(1772)]
 fn PoolN_postcreate_split_system() {post_create(FreshPdaPreparationV1::CreateOrAllocateSystemOwned)}
 #[kani::proof]
 #[kani::unwind(196)]
 fn PoolN_alias_any_two_of_fourteen() {
  let id=Pubkey::new_from_array([7;32]);let cpkey=Pubkey::new_from_array([8;32]);
  let mut bytes:[u8;192]=kani::any();let before=bytes[0];let mut balance:u64=kani::any();let original_balance=balance;
  let account=AccountInfo::new(&cpkey,kani::any(),kani::any(),&mut balance,&mut bytes,&id,false,0);
  let keys:[Pubkey;14]=core::array::from_fn(|i|Pubkey::new_from_array([20+i as u8;32]));
  let mut balances=[0u64;14];let mut dummy=[[0u8;0];14];let mut accounts=Vec::new();
  for ((key,bal),data) in keys.iter().zip(balances.iter_mut()).zip(dummy.iter_mut()) {
   accounts.push(AccountInfo::new(key,false,false,bal,data,&id,false,0));
  }
  let first=usize::from(kani::any::<u8>());let second=usize::from(kani::any::<u8>());
  kani::assume(first<14 && second<14 && first!=second);
  accounts[first]=account.clone();accounts[second]=account.clone();
  assert_eq!(require_unique_accounts(&accounts),Err(ProgramError::InvalidArgument));
  kani::cover!(first==0 && second==13,"distant checkpoint alias rejected");
  drop(accounts);drop(account);assert_eq!(bytes[0],before);assert_eq!(balance,original_balance);
 }
}
