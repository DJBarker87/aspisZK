#![allow(dead_code)]
use solana_program::{account_info::AccountInfo,pubkey::Pubkey,program_error::ProgramError};
#[cfg(kani)] mod proofs {
 use super::*;
 fn shared_snapshot<const N:usize>() {
  let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());
  let mut lamports=kani::any();let before_lamports=lamports;
  let mut bytes:[u8;N]=kani::any();let selected:usize=kani::any();kani::assume(selected<N);
  let account=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());
  let alias=account.clone();
  let data=account.try_borrow_data().unwrap();
  let second=alias.try_borrow_data().unwrap();
  let snapshot=data.to_vec();
  assert_eq!(snapshot.len(),N);assert_eq!(snapshot[selected],data[selected]);
  assert_eq!(snapshot[selected],second[selected]);
  assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
  drop(second);drop(data);
  assert_eq!(account.try_borrow_data().unwrap()[selected],snapshot[selected]);
  assert_eq!(**account.try_borrow_lamports().unwrap(),before_lamports);
  assert!(alias.try_borrow_mut_data().is_ok());
  kani::cover!(snapshot[selected]!=0,"arbitrary nonzero snapshot byte");
 }
 #[kani::proof] #[kani::unwind(3)]
 fn public_owned_snapshot_actual_sdk() {shared_snapshot::<1880>();}
 #[kani::proof] #[kani::unwind(3)]
 fn proof_owned_snapshot_actual_sdk() {shared_snapshot::<58295>();}
}
