use super::*;
fn NCL_account(length:Result<usize,ProgramError>,s:bool,w:bool,e:bool)->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array([0;32]),owner:Pubkey::new_from_array([0;32]),is_signer:s,is_writable:w,executable:e,length,bytes:Err(ProgramError::InvalidAccountData)}}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_length_ok(){let n:usize=kani::any();let a=NCL_account(Ok(n),false,false,false);assert_eq!(a.data_len(),Ok(n));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_length_ok_wrong(){let a=NCL_account(Ok(7),false,false,false);assert_eq!(a.data_len(),Ok(8));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_length_err(){let x:u32=kani::any();let a=NCL_account(Err(ProgramError::Custom(x)),false,false,false);assert_eq!(a.data_len(),Err(ProgramError::Custom(x)));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_length_err_wrong(){let a=NCL_account(Err(ProgramError::Custom(17)),false,false,false);assert_eq!(a.data_len(),Err(ProgramError::Custom(18)));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_key(){let a=NCL_account(Ok(0),false,false,false);assert!(core::ptr::eq(a.key(),&a.key));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_key_wrong(){let a=NCL_account(Ok(0),false,false,false);assert!(core::ptr::eq(a.key(),&a.owner));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owner(){let a=NCL_account(Ok(0),false,false,false);assert!(core::ptr::eq(a.owner(),&a.owner));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owner_wrong(){let a=NCL_account(Ok(0),false,false,false);assert!(core::ptr::eq(a.owner(),&a.key));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_readonly(){let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let a=NCL_account(Ok(0),s,w,e);assert_eq!(require_readonly_buffer(&a),if s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_readonly_wrong(){let a=NCL_account(Ok(0),false,true,false);assert_eq!(require_readonly_buffer(&a),Ok(()));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_err(){let x:u32=kani::any();let mut a=NCL_account(Ok(0),false,false,false);a.bytes=Err(ProgramError::Custom(x));assert_eq!(a.data(),Err(ProgramError::Custom(x)));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_err_wrong(){let mut a=NCL_account(Ok(0),false,false,false);a.bytes=Err(ProgramError::Custom(7));assert_eq!(a.data(),Err(ProgramError::Custom(8)));}
#[kani::proof] #[kani::unwind(3)]
fn NCL_zero_one(){let x:u8=kani::any();assert_eq!(require_zero(&[x]),if x==0{Ok(())}else{Err(ProgramError::AccountAlreadyInitialized)});}
#[kani::proof] #[kani::unwind(3)]
fn NCL_zero_one_wrong(){assert_eq!(require_zero(&[1]),Ok(()));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_checkpoint_meta(){let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let required:bool=kani::any();let n:usize=kani::any();let fail:bool=kani::any();let code:u32=kani::any();let length=if fail{Err(ProgramError::Custom(code))}else{Ok(n)};let a=NCL_account(length,signer,writable,executable);let program=Pubkey::new_from_array([0;32]);let expected=if signer||executable||writable!=required{Err(ProgramError::InvalidAccountData)}else if fail{Err(ProgramError::Custom(code))}else if n!=1768{Err(ProgramError::InvalidAccountData)}else{Ok(())};assert_eq!(require_verifier_checkpoint(&a,&program,required),expected);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_checkpoint_meta_wrong(){let a=NCL_account(Ok(1767),false,true,false);let p=Pubkey::new_from_array([0;32]);assert_eq!(require_verifier_checkpoint(&a,&p,true),Ok(()));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_checkpoint_owner(){let x:u8=kani::any();let mut a=NCL_account(Ok(1768),false,true,false);let mut bytes=[0u8;32];bytes[0]=x;a.owner=Pubkey::new_from_array(bytes);let p=Pubkey::new_from_array([0;32]);assert_eq!(require_verifier_checkpoint(&a,&p,true),if x==0{Ok(())}else{Err(ProgramError::InvalidAccountData)});}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_checkpoint_owner_wrong(){let mut a=NCL_account(Ok(1768),false,true,false);let mut bytes=[0u8;32];bytes[0]=1;a.owner=Pubkey::new_from_array(bytes);let p=Pubkey::new_from_array([0;32]);assert_eq!(require_verifier_checkpoint(&a,&p,true),Ok(()));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_empty(){let mut a=NCL_account(Ok(0),false,false,false);a.bytes=Ok(Vec::new());let data=a.data().unwrap();assert_eq!(data.len(),0);assert_eq!(data.as_ptr(),a.bytes.as_ref().unwrap().as_ptr());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_empty_wrong(){let mut a=NCL_account(Ok(0),false,false,false);a.bytes=Ok(Vec::new());assert_eq!(a.data().unwrap().len(),1);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owned_count(){let p=Pubkey::new_from_array([0;32]);let split:u8=kani::any();kani::assume(split==10||split==11);assert_eq!(stage1_owned(&p,&[],&[3,split]),Err(ProgramError::InvalidInstructionData));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owned_count_wrong(){let p=Pubkey::new_from_array([0;32]);assert!(stage1_owned(&p,&[],&[3,10]).is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_length_reject(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let x:u8=kani::any();let mut bytes=[x];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);let saved=snapshot(&a,2,3);assert_eq!(saved.length,Ok(1));assert_eq!(saved.bytes,Err(ProgramError::InvalidAccountData));assert_eq!(saved.key,key);assert_eq!(saved.owner,owner);assert!(a.data.try_borrow_mut().is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_length_reject_wrong(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let mut bytes=[1];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);assert!(snapshot(&a,2,3).bytes.is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_borrow_error(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let mut bytes=[1];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);let held=a.try_borrow_mut_data().unwrap();let saved=snapshot(&a,1,1);assert_eq!(saved.length,Err(ProgramError::AccountBorrowFailed));assert_eq!(saved.bytes,Err(ProgramError::AccountBorrowFailed));drop(held);assert!(a.try_borrow_mut_data().is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_borrow_error_wrong(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let mut bytes=[1];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);let held=a.try_borrow_mut_data().unwrap();assert!(snapshot(&a,1,1).bytes.is_ok());drop(held);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,crate::NCL_copy::KMX_to_vec)]
fn NCL_snapshot_one(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let x:u8=kani::any();let mut bytes=[x];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);let saved=snapshot(&a,1,1);assert_eq!(saved.length,Ok(1));let v=saved.bytes.unwrap();assert_eq!(v.len(),1);assert_eq!(v[0],x);assert_eq!(a.try_borrow_data().unwrap()[0],x);assert!(a.try_borrow_mut_data().is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::to_vec,crate::NCL_copy::KMX_to_vec)]
fn NCL_snapshot_one_wrong(){let key=Pubkey::new_from_array([7;32]);let owner=Pubkey::new_from_array([9;32]);let mut lamports=0;let mut bytes=[7];let a=AccountInfo::new(&key,false,false,&mut lamports,&mut bytes,&owner,false,0);assert_eq!(snapshot(&a,1,1).bytes.unwrap()[0],8);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owned_bad_instruction(){let p=Pubkey::new_from_array([0;32]);let accounts=[NCL_account(Ok(0),false,false,false),NCL_account(Ok(0),false,false,false),NCL_account(Ok(0),false,false,false)];let tag:u8=kani::any();kani::assume(tag!=3);let k:u8=kani::any();assert_eq!(stage1_owned(&p,&accounts,&[tag,k]),Err(ProgramError::InvalidInstructionData));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_owned_bad_instruction_wrong(){let p=Pubkey::new_from_array([0;32]);let accounts=[NCL_account(Ok(0),false,false,false),NCL_account(Ok(0),false,false,false),NCL_account(Ok(0),false,false,false)];assert!(stage1_owned(&p,&accounts,&[2,10]).is_ok());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_one(){let x:u8=kani::any();let mut a=NCL_account(Ok(1),false,false,false);let mut bytes=Vec::with_capacity(1);bytes.push(x);a.bytes=Ok(bytes);let slice=a.data().unwrap();assert_eq!(slice.len(),1);assert_eq!(slice[0],x);assert_eq!(slice.as_ptr(),a.bytes.as_ref().unwrap().as_ptr());}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_data_one_wrong(){let mut a=NCL_account(Ok(1),false,false,false);let mut bytes=Vec::with_capacity(1);bytes.push(7);a.bytes=Ok(bytes);assert_eq!(a.data().unwrap()[0],8);}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_meta(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports=0;let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let rent:u64=kani::any();let mut bytes=[];let a=AccountInfo::new(&key,s,w,&mut lamports,&mut bytes,&owner,e,rent);let saved=snapshot(&a,1,2);assert_eq!(saved.key,key);assert_eq!(saved.owner,owner);assert_eq!(saved.is_signer,s);assert_eq!(saved.is_writable,w);assert_eq!(saved.executable,e);assert_eq!(saved.length,Ok(0));assert_eq!(saved.bytes,Err(ProgramError::InvalidAccountData));}
#[kani::proof] #[kani::unwind(34)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::NCL_copy::KMX_copy_nonoverlapping)]
fn NCL_snapshot_meta_wrong(){let key=Pubkey::new_from_array([0;32]);let owner=Pubkey::new_from_array([0;32]);let mut lamports=0;let mut bytes=[];let a=AccountInfo::new(&key,true,false,&mut lamports,&mut bytes,&owner,false,0);assert!(!snapshot(&a,1,2).is_signer);}
