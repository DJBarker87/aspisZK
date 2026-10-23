#[cfg(kani)] mod proofs {
use super::*;
fn statement()->PoolV1PairForestTerminalStatementV1 {
 // Every bit pattern is valid for these three reference-free, enum-free
 // structs (only u8/u32/u64, M31(u32), fixed arrays and their structs).
 let common:PoolV1PairForestTerminalCommonV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1PairForestTerminalCommonV1>()]>())};
 if kani::any() {
  let public:PoolV1PrivateTransferPublicV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1PrivateTransferPublicV1>()]>())};
  PoolV1PairForestTerminalStatementV1::PrivateTransfer{common,public}
 } else {
  let public:PoolV1WithdrawalPublicV1=unsafe{std::mem::transmute(kani::any::<[u8;std::mem::size_of::<PoolV1WithdrawalPublicV1>()]>())};
  PoolV1PairForestTerminalStatementV1::Withdrawal{common,public}
 }
}
#[kani::proof]
#[kani::unwind(1772)]
fn actual_sdk_stage1_binding() {
 let program=Pubkey::new_from_array([4;32]);
 let keys:[Pubkey;3]=[Pubkey::new_from_array([1;32]),Pubkey::new_from_array([2;32]),Pubkey::new_from_array([3;32])];
 let owner=Pubkey::new_from_array([5;32]);
 let mut lamports=[0u64;3];
 let [ref mut l0,ref mut l1,ref mut l2]=lamports;
 // One arbitrary selected cell covers the byte-oblivious SDK/control spine;
 // this harness does not claim an all-byte parser/validator certificate.
 let mut proof=vec![0u8;688+PROOF]; proof[696]=2;
 proof[0]=kani::any();proof[696]=kani::any();
 let mut public:[u8;16]=kani::any();
 let mut checkpoint=vec![0u8;CP];
 let occupied:bool=kani::any();if occupied {checkpoint[0]=1;}
 let observed:usize=kani::any();kani::assume(observed<CP);
 let before=checkpoint[observed];
 let proof_ptr=proof.as_ptr() as usize;let public_ptr=public.as_ptr() as usize;
 let p=Plan{statement:statement(),fail:kani::any(),output:kani::any(),output_len:if kani::any(){CP}else{0},public_ptr,public_len:public.len(),proof_ptr,k:if kani::any(){10}else{11}};
 unsafe{PLAN=Some(p);CALLS=0;}
 let a0=AccountInfo::new(&keys[0],false,false,l0,&mut proof,&owner,false,0);
 let a1=AccountInfo::new(&keys[1],false,false,l1,&mut public,&owner,false,0);
 let a2=AccountInfo::new(&keys[2],false,true,l2,&mut checkpoint,&program,false,0);
 let accounts=[a0,a1,a2];
 // Live immutable or mutable borrows exercise real RefCell rejection,
 // with guards retained until after the actual full stage1 call.
 let held_shared:Option<Ref<'_,&mut [u8]>>=if kani::any(){Some(accounts[2].try_borrow_data().unwrap())}else{None};
 let held_mut:Option<RefMut<'_,&mut [u8]>>=if kani::any(){Some(accounts[1].try_borrow_mut_data().unwrap())}else{None};
 let data=[3,p.k as u8];
 let result=adapter::run(&program,&accounts,&data);
 drop(held_shared);drop(held_mut);
 let after=accounts[2].try_borrow_data().unwrap();
 if result.is_ok(){assert_eq!(unsafe{CALLS},1);assert_eq!(p.output_len,CP);assert_eq!(after[observed],p.output);}
 else {assert_eq!(after[observed],before);}
 assert!(accounts[0].try_borrow_mut_data().is_ok());
 assert!(accounts[1].try_borrow_mut_data().is_ok());
 drop(after);assert!(accounts[2].try_borrow_mut_data().is_ok());
}
#[kani::proof]
#[kani::unwind(20)]
fn sdk_immutable_alias_and_writeback() {
 let key=Pubkey::new_from_array([1;32]);let owner=Pubkey::new_from_array([2;32]);
 let mut lamports=0;let mut data:[u8;16]=kani::any();let original=data;
 let account=AccountInfo::new(&key,false,false,&mut lamports,&mut data,&owner,false,0);
 let alias=account.clone();
 let reader=account.try_borrow_data().unwrap();
 assert!(matches!(alias.try_borrow_mut_data(),Err(ProgramError::AccountBorrowFailed)));
 assert_eq!(&**reader,&original[..]);
 let reader2=alias.try_borrow_data().unwrap();assert_eq!(reader.as_ptr(),reader2.as_ptr());
 drop(reader2);drop(reader);
 let replacement:[u8;16]=kani::any();
 let mut writer=alias.try_borrow_mut_data().unwrap();
 assert!(matches!(account.try_borrow_data(),Err(ProgramError::AccountBorrowFailed)));
 writer.copy_from_slice(&replacement);drop(writer);
 assert_eq!(&**account.try_borrow_data().unwrap(),&replacement[..]);
}
}
