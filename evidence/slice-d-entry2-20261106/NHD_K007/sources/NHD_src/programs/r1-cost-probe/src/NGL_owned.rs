use super::*;
include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs"));
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array(kani::any()),owner:Pubkey::new_from_array(kani::any()),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(kani::any()),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_account_wrong(){let a=core::mem::ManuallyDrop::new(account());let k=Pubkey::new_from_array(kani::any());let expected=if a.owner!=k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())};let r=require_readonly_account(&a,&k);assert!((r==expected) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_deferred(){let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_deferred_wrong(){let mut a=core::mem::ManuallyDrop::new(account());let n:usize=kani::any();let tag:u8=kani::any();kani::assume(tag<3);a.length=if tag==0{Ok(n)}else if tag==1{Err(ProgramError::AccountBorrowFailed)}else{Err(ProgramError::InvalidAccountData)};let r=a.data_len();let exact=match tag{0=>matches!(r,Ok(v)if v==n),1=>matches!(r,Err(ProgramError::AccountBorrowFailed)),_=>matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_deferred(){let mut a=core::mem::ManuallyDrop::new(account());let borrow:bool=kani::any();a.bytes=Err(if borrow{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData});let r=a.data();let exact=if borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_deferred_wrong(){let mut a=core::mem::ManuallyDrop::new(account());let borrow:bool=kani::any();a.bytes=Err(if borrow{ProgramError::AccountBorrowFailed}else{ProgramError::InvalidAccountData});let r=a.data();let exact=if borrow{matches!(r,Err(ProgramError::AccountBorrowFailed))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_meta(){let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact != cfg!(NGL_invert));}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_meta_wrong(){let owner:[u8;32]=kani::any();let program:[u8;32]=kani::any();let mut a=core::mem::ManuallyDrop::new(account());a.owner=Pubkey::new_from_array(owner);let writable:bool=kani::any();let n:usize=kani::any();let error:bool=kani::any();a.length=if error{Err(ProgramError::AccountBorrowFailed)}else{Ok(n)};let invalid=owner!=program||a.is_signer||a.executable||a.is_writable!=writable;let r=require_verifier_checkpoint(&a,&Pubkey::new_from_array(program),writable);let exact=if invalid{matches!(r,Err(ProgramError::InvalidAccountData))}else if error{matches!(r,Err(ProgramError::AccountBorrowFailed))}else if n!=1768{matches!(r,Err(ProgramError::InvalidAccountData))}else{matches!(r,Ok(()))};assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count0(){let key=Pubkey::new_from_array(kani::any());let data=&[3u8,10][..];let r=stage1(&key,&[],data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count0_wrong(){let key=Pubkey::new_from_array(kani::any());let data=&[3u8,10][..];let r=stage1(&key,&[],data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count1(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 1, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count1_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 1, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count2(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 2, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count2_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 2, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count4(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 4, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage1_count4_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 4, _>(|_|a.clone());let data=&[3u8,10][..];let r=stage1(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count0(){let key=Pubkey::new_from_array(kani::any());let data=&b"ASQ8"[..];let r=stage2(&key,&[],data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count0_wrong(){let key=Pubkey::new_from_array(kani::any());let data=&b"ASQ8"[..];let r=stage2(&key,&[],data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count1(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 1, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count1_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 1, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count6(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 6, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count6_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 6, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count8(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 8, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn stage2_count8_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;1]=kani::any();let a=AccountInfo::new(&key,kani::any(),kani::any(),&mut lamports,&mut bytes,&owner,kani::any(),kani::any());let accounts=core::array::from_fn::<_, 8, _>(|_|a.clone());let data=&b"ASQ8"[..];let r=stage2(&key,&accounts,data);assert!(matches!(r,Err(ProgramError::InvalidInstructionData)) == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn snapshot_rejected_length(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;5]=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes,&owner,executable,rent);let result=core::mem::ManuallyDrop::new(snapshot(&a,1768,58295));let metadata=result.key==key&&result.owner==owner&&result.is_signer==signer&&result.is_writable==writable&&result.executable==executable;let exact=metadata&&matches!(result.length,Ok(5))&&matches!(result.bytes,Err(ProgramError::InvalidAccountData));assert!(exact != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn snapshot_rejected_length_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;5]=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes,&owner,executable,rent);let result=core::mem::ManuallyDrop::new(snapshot(&a,1768,58295));let metadata=result.key==key&&result.owner==owner&&result.is_signer==signer&&result.is_writable==writable&&result.executable==executable;let exact=metadata&&matches!(result.length,Ok(5))&&matches!(result.bytes,Err(ProgramError::InvalidAccountData));assert!(exact == cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn snapshot_borrow_error(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;5]=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes,&owner,executable,rent);let held=a.try_borrow_mut_data().unwrap();let result=core::mem::ManuallyDrop::new(snapshot(&a,1768,58295));let metadata=result.key==key&&result.owner==owner&&result.is_signer==signer&&result.is_writable==writable&&result.executable==executable;let exact=metadata&&matches!(result.length,Err(ProgramError::AccountBorrowFailed))&&matches!(result.bytes,Err(ProgramError::AccountBorrowFailed));drop(held);assert!(exact != cfg!(NGL_invert));}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn snapshot_borrow_error_wrong(){let key=Pubkey::new_from_array(kani::any());let owner=Pubkey::new_from_array(kani::any());let mut lamports:u64=kani::any();let mut bytes:[u8;5]=kani::any();let signer:bool=kani::any();let writable:bool=kani::any();let executable:bool=kani::any();let rent:u64=kani::any();let a=AccountInfo::new(&key,signer,writable,&mut lamports,&mut bytes,&owner,executable,rent);let held=a.try_borrow_mut_data().unwrap();let result=core::mem::ManuallyDrop::new(snapshot(&a,1768,58295));let metadata=result.key==key&&result.owner==owner&&result.is_signer==signer&&result.is_writable==writable&&result.executable==executable;let exact=metadata&&matches!(result.length,Err(ProgramError::AccountBorrowFailed))&&matches!(result.bytes,Err(ProgramError::AccountBorrowFailed));drop(held);assert!(exact == cfg!(NGL_invert));}

pub(super) fn zero_frame(after:*const u8,after_len:usize,before:*const u8,before_len:usize){assert_eq!(after,unsafe{before.add(1)});assert_eq!(after_len,before_len-1);}
fn zero_frame_wrong(after:*const u8,after_len:usize,before:*const u8,before_len:usize){assert!(after!=unsafe{before.add(1)}||after_len!=before_len-1);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn zero_iteration(){let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=1768&&len<=1768-start);let input=&bytes[start..start+len];let r=require_zero(input);let expected=if len==0||input[0]==0{Ok(())}else{Err(ProgramError::AccountAlreadyInitialized)};assert_eq!(r,expected);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
#[kani::stub(zero_frame,zero_frame_wrong)]
fn zero_iteration_frame_wrong(){let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=1768&&len<=1768-start);let input=&bytes[start..start+len];let r=require_zero(input);let expected=if len==0||input[0]==0{Ok(())}else{Err(ProgramError::AccountAlreadyInitialized)};assert_eq!(r,expected);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn zero_iteration_result_wrong(){let bytes:[u8;1768]=kani::any();let start:usize=kani::any();let len:usize=kani::any();kani::assume(start<=1768&&len<=1768-start);let input=&bytes[start..start+len];let r=require_zero(input);let expected=if len==0||input[0]==0{Ok(())}else{Err(ProgramError::AccountAlreadyInitialized)};assert_ne!(r,expected);}

pub(super) fn length_domain(r:&Result<usize,ProgramError>)->bool{matches!(r,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData))}
pub(super) fn checkpoint_domain(a:&OwnedAccount)->bool{matches!(a.length,Ok(_)|Err(ProgramError::AccountBorrowFailed))}
pub(super) fn readonly_ref(a:&OwnedAccount,k:&Pubkey)->ProgramResult{if a.owner!=*k||a.is_signer||a.is_writable||a.executable{Err(ProgramError::InvalidAccountData)}else{Ok(())}}
pub(super) fn checkpoint_ref(a:&OwnedAccount,k:&Pubkey,w:bool)->ProgramResult{if a.owner!=*k||a.is_signer||a.executable||a.is_writable!=w{Err(ProgramError::InvalidAccountData)}else{match a.length{Err(ProgramError::AccountBorrowFailed)=>Err(ProgramError::AccountBorrowFailed),Ok(1768)=>Ok(()),_=>Err(ProgramError::InvalidAccountData)}}}
#[kani::proof_for_contract(require_readonly_account)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn readonly_contract(){let mut a=core::mem::ManuallyDrop::new(account());let shape:u8=kani::any();kani::assume(shape<11);match shape{0=>{let v=kani::vec::exact_vec::<u8,58295>();a.length=Ok(58295);a.bytes=Ok(v);},1=>{let v=kani::vec::exact_vec::<u8,1768>();a.length=Ok(1768);a.bytes=Ok(v);},2=>{let v=kani::vec::exact_vec::<u8,1880>();a.length=Ok(1880);a.bytes=Ok(v);},3=>{let v=kani::vec::exact_vec::<u8,384>();a.length=Ok(384);a.bytes=Ok(v);},4=>{let v=kani::vec::exact_vec::<u8,192>();a.length=Ok(192);a.bytes=Ok(v);},5=>{let v=kani::vec::exact_vec::<u8,768>();a.length=Ok(768);a.bytes=Ok(v);},6=>{let v=kani::vec::exact_vec::<u8,128>();a.length=Ok(128);a.bytes=Ok(v);},7=>{let v=kani::vec::exact_vec::<u8,256>();a.length=Ok(256);a.bytes=Ok(v);},8=>{let v=kani::vec::exact_vec::<u8,320>();a.length=Ok(320);a.bytes=Ok(v);},9=>{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);},_=>{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}}let p=Pubkey::new_from_array(kani::any());let _=core::mem::ManuallyDrop::new(require_readonly_account(&a,&p));}
#[kani::proof_for_contract(OwnedAccount::data_len)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=NGL_CAP);let mut v=kani::vec::exact_vec::<u8,NGL_CAP>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);}
let _=core::mem::ManuallyDrop::new(a.data_len());}
#[kani::proof_for_contract(require_verifier_checkpoint)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=NGL_CAP);let mut v=kani::vec::exact_vec::<u8,NGL_CAP>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);}
let _=core::mem::ManuallyDrop::new(require_verifier_checkpoint(&a,&Pubkey::new_from_array(kani::any()),kani::any()));}

pub(super) fn same_length(a:&Result<usize,ProgramError>,b:&Result<usize,ProgramError>)->bool{match(a,b){(Ok(x),Ok(y))=>x==y,(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))=>true,(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))=>true,_=>false}}
pub(super) fn same_program_result(a:&ProgramResult,b:&ProgramResult)->bool{match(a,b){(Ok(()),Ok(()))=>true,(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))=>true,(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))=>true,_=>false}}

fn length_observation(r:Result<usize,ProgramError>)->[usize;2]{match r{Ok(n)=>[0,n],Err(ProgramError::AccountBorrowFailed)=>[1,0],Err(ProgramError::InvalidAccountData)=>[2,0],Err(_)=>[3,0]}}
fn length_observation_ref(a:&OwnedAccount)->[usize;2]{match a.length{Ok(n)=>[0,n],Err(ProgramError::AccountBorrowFailed)=>[1,0],Err(ProgramError::InvalidAccountData)=>[2,0],_=>[3,0]}}
#[kani::requires(length_domain(&a.length))]
#[kani::ensures(|r| (*r==length_observation_ref(a)) != cfg!(NGL_invert))]
#[kani::modifies()]
fn observed_length(a:&OwnedAccount)->[usize;2]{length_observation(a.data_len())}
#[kani::proof_for_contract(observed_length)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_observed_contract(){let mut a=core::mem::ManuallyDrop::new(account());let tag:u8=kani::any();kani::assume(tag<3);a.length=match tag{0=>Ok(kani::any()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};let _=observed_length(&a);}

#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_full_payload(){let v=kani::vec::exact_vec::<u8,58295>();let mut a=core::mem::ManuallyDrop::new(account());a.bytes=Ok(v);let original=a.bytes.as_ref().unwrap();let ptr=original.as_ptr();let len=original.len();let result=a.data();let exact=matches!(result,Ok(slice) if slice.as_ptr()==ptr&&slice.len()==len);assert!(exact);}
#[kani::proof] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_full_payload_wrong(){let v=kani::vec::exact_vec::<u8,58295>();let mut a=core::mem::ManuallyDrop::new(account());a.bytes=Ok(v);let original=a.bytes.as_ref().unwrap();let ptr=original.as_ptr();let len=original.len();let result=a.data();let exact=matches!(result,Ok(slice) if slice.as_ptr()==ptr&&slice.len()==len);assert!(!exact);}

#[cfg(any())]
#[kani::proof_for_contract(OwnedAccount::data_len)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_contract_ok(){let mut a=core::mem::ManuallyDrop::new(account());a.length=Ok(kani::any());let _=a.data_len();}

#[cfg(any())]
#[kani::proof_for_contract(OwnedAccount::data_len)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_contract_invalid(){let mut a=core::mem::ManuallyDrop::new(account());a.length=Err(ProgramError::InvalidAccountData);let _=a.data_len();}

#[derive(PartialEq,Eq)]
struct NGL_Frame{key:[u8;32],owner:[u8;32],signer:bool,writable:bool,executable:bool,length_tag:u8,length_value:usize,bytes_tag:u8,pointer:usize,length:usize,capacity:usize,cell:u8}
fn frame(a:&OwnedAccount,j:usize)->NGL_Frame{
 let(lt,lv)=match &a.length{Ok(n)=>(0,*n),Err(ProgramError::AccountBorrowFailed)=>(1,0),Err(ProgramError::InvalidAccountData)=>(2,0),_=>(3,0)};
 let(bt,p,n,c,v)=match &a.bytes{Ok(b)=>(0,b.as_ptr()as usize,b.len(),b.capacity(),if b.is_empty(){0}else{b[j]}),Err(ProgramError::AccountBorrowFailed)=>(1,0,0,0,0),Err(ProgramError::InvalidAccountData)=>(2,0,0,0,0),_=>(3,0,0,0,0)};
 NGL_Frame{key:a.key.to_bytes(),owner:a.owner.to_bytes(),signer:a.is_signer,writable:a.is_writable,executable:a.executable,length_tag:lt,length_value:lv,bytes_tag:bt,pointer:p,length:n,capacity:c,cell:v}
}
fn record_account(checkpoint:bool)->core::mem::ManuallyDrop<OwnedAccount>{
 let mut a=account();let length_case:u8=kani::any();kani::assume(length_case<if checkpoint{2}else{3});a.length=match length_case{0=>Ok(kani::any()),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};
 let n:usize=kani::any();kani::assume(n<=58295);let mut bytes=kani::vec::exact_vec::<u8,58295>();bytes.truncate(n);let bytes_case:u8=kani::any();kani::assume(bytes_case<3);a.bytes=match bytes_case{0=>Ok(bytes),1=>Err(ProgramError::AccountBorrowFailed),_=>Err(ProgramError::InvalidAccountData)};
 core::mem::ManuallyDrop::new(a)
}

fn bytes_domain(a:&OwnedAccount)->bool{matches!(&a.bytes,Ok(_)|Err(ProgramError::AccountBorrowFailed)|Err(ProgramError::InvalidAccountData))}
#[kani::requires(snapshot_domain(a))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn length_record(a:&OwnedAccount)->bool{let mut tag:u8=3;let mut value:usize=0;match &a.length{Ok(n)=>{tag=0;value=*n},Err(ProgramError::AccountBorrowFailed)=>tag=1,Err(ProgramError::InvalidAccountData)=>tag=2,Err(_)=>{}};if cfg!(NGL_invert){tag^=128;}let r=core::mem::ManuallyDrop::new(a.data_len());match &*r{Ok(n)=>tag==0&&*n==value,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,Err(_)=>false}}
#[kani::proof_for_contract(length_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn length_record_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(kani::any());a.bytes=Ok(v);}
let _=length_record(&a);}
#[kani::requires(snapshot_domain(a))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn data_record(a:&OwnedAccount)->bool{let(tag,p,n)=match &a.bytes{Ok(v)=>(0,v.as_ptr()as usize,v.len()),Err(ProgramError::AccountBorrowFailed)=>(1,0,0),Err(ProgramError::InvalidAccountData)=>(2,0,0),_=>(3,0,0)};let mut expected=tag;if cfg!(NGL_invert){expected^=128;}let r=core::mem::ManuallyDrop::new(a.data());match &*r{Ok(b)=>expected==0&&b.as_ptr()as usize==p&&b.len()==n,Err(ProgramError::AccountBorrowFailed)=>expected==1,Err(ProgramError::InvalidAccountData)=>expected==2,Err(_)=>false}}
#[kani::proof_for_contract(data_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_record_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(kani::any());a.bytes=Ok(v);}
let _=data_record(&a);}
#[kani::requires(snapshot_domain(a))] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn checkpoint_record(a:&OwnedAccount,program:&Pubkey,writable:bool)->bool{let invalid=a.owner!=*program||a.is_signer||a.executable||a.is_writable!=writable;let mut tag=if invalid{2}else{match &a.length{Err(ProgramError::AccountBorrowFailed)=>1,Ok(n)if *n==1768=>0,_=>2}};if cfg!(NGL_invert){tag^=128;}let r=core::mem::ManuallyDrop::new(require_verifier_checkpoint(a,program,writable));match &*r{Ok(())=>tag==0,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,Err(_)=>false}}
#[kani::proof_for_contract(checkpoint_record)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn checkpoint_record_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=58295);let mut v=kani::vec::exact_vec::<u8,58295>();v.truncate(n);a.length=Ok(kani::any());a.bytes=Ok(v);}
let program=Pubkey::new_from_array(kani::any());let _=checkpoint_record(&a,&program,kani::any());}

pub(super) fn snapshot_domain(a:&OwnedAccount)->bool{match(&a.length,&a.bytes){(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))=>true,(Ok(_),Err(ProgramError::InvalidAccountData))=>true,(Ok(n),Ok(v))=>*n==v.len()&&v.len()<=58295,_=>false}}

struct NGL_KeyLog{count:usize,left:*const Pubkey,right:*const Pubkey,left_bytes:[u8;32],right_bytes:[u8;32]}
fn distinct_step<const N:usize>(accounts:&[&OwnedAccount;N],index:usize,mut previous:usize,log:&mut NGL_KeyLog)->(ProgramResult,usize){
 if previous<index{
  let left=accounts[previous].key();let right=accounts[index].key();
  log.count=2;log.left=left as *const Pubkey;log.right=right as *const Pubkey;log.left_bytes=left.to_bytes();log.right_bytes=right.to_bytes();
  if left==right{return(Err(ProgramError::InvalidArgument),previous);}
  previous+=1;
 }
 (Ok(()),previous)
}
#[kani::requires(index<3&&previous<=index)] #[kani::ensures(|r|*r != cfg!(NGL_guard_false))] #[kani::modifies()]
fn distinct_record3(a:&[OwnedAccount;3],index:usize,previous:usize)->bool{
 let refs=core::array::from_fn::<_,3,_>(|i|&a[i]);let mut log=NGL_KeyLog{count:0,left:core::ptr::null(),right:core::ptr::null(),left_bytes:[0;32],right_bytes:[0;32]};let outcome=core::mem::ManuallyDrop::new(distinct_step(&refs,index,previous,&mut log));let(r,next)=(&outcome.0,outcome.1);
 if cfg!(NGL_invert){log.left=log.left.wrapping_add(1);}
 let equal=previous<index&&a[previous].key==a[index].key;let exact=if equal{matches!(r,Err(ProgramError::InvalidArgument))&&next==previous}else{matches!(r,Ok(()))&&next==if previous<index{previous+1}else{previous}};
 let calls=if previous<index{log.count==2&&log.left==&a[previous].key as *const Pubkey&&log.right==&a[index].key as *const Pubkey&&log.left_bytes==a[previous].key.to_bytes()&&log.right_bytes==a[index].key.to_bytes()}else{log.count==0&&log.left.is_null()&&log.right.is_null()};exact&&calls
}
#[kani::proof_for_contract(distinct_record3)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn distinct3_contract(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,3,_>(|_|account()));let index:usize=kani::any();let previous:usize=kani::any();kani::assume(index<3&&previous<=index);#[cfg(NGL_distinct_exit)] kani::assume(previous==index);let _=distinct_record3(&a,index,previous);}

#[kani::requires(index<7&&previous<=index)] #[kani::ensures(|r|*r)] #[kani::modifies()]
fn distinct_record7(a:&[OwnedAccount;7],index:usize,previous:usize)->bool{
 let refs=core::array::from_fn::<_,7,_>(|i|&a[i]);let mut log=NGL_KeyLog{count:0,left:core::ptr::null(),right:core::ptr::null(),left_bytes:[0;32],right_bytes:[0;32]};let outcome=core::mem::ManuallyDrop::new(distinct_step(&refs,index,previous,&mut log));let(r,next)=(&outcome.0,outcome.1);
 if cfg!(NGL_invert){log.left=log.left.wrapping_add(1);}
 let equal=previous<index&&a[previous].key==a[index].key;let exact=if equal{matches!(r,Err(ProgramError::InvalidArgument))&&next==previous}else{matches!(r,Ok(()))&&next==if previous<index{previous+1}else{previous}};
 let calls=if previous<index{log.count==2&&log.left==&a[previous].key as *const Pubkey&&log.right==&a[index].key as *const Pubkey&&log.left_bytes==a[previous].key.to_bytes()&&log.right_bytes==a[index].key.to_bytes()}else{log.count==0&&log.left.is_null()&&log.right.is_null()};exact&&calls
}
#[kani::proof_for_contract(distinct_record7)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn distinct7_contract(){let a=core::mem::ManuallyDrop::new(core::array::from_fn::<_,7,_>(|_|account()));let index:usize=kani::any();let previous:usize=kani::any();kani::assume(index<7&&previous<=index);let _=distinct_record7(&a,index,previous);}

pub(super) fn data_matches(r:&Result<&[u8],ProgramError>,a:&OwnedAccount)->bool{match(r,&a.bytes){(Ok(b),Ok(v))=>b.as_ptr()==v.as_ptr()&&b.len()==v.len(),(Err(ProgramError::AccountBorrowFailed),Err(ProgramError::AccountBorrowFailed))=>true,(Err(ProgramError::InvalidAccountData),Err(ProgramError::InvalidAccountData))=>true,_=>false}}
pub(super) fn checkpoint_matches(r:&ProgramResult,a:&OwnedAccount,p:&Pubkey,w:bool)->bool{let tag=if a.owner!=*p||a.is_signer||a.executable||a.is_writable!=w{2}else{match &a.length{Ok(n)if *n==1768=>0,Err(ProgramError::AccountBorrowFailed)=>1,_=>2}};match r{Ok(())=>tag==0,Err(ProgramError::AccountBorrowFailed)=>tag==1,Err(ProgramError::InvalidAccountData)=>tag==2,_=>false}}

#[kani::proof_for_contract(OwnedAccount::data)] #[kani::unwind(35)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn data_actual_contract(){let mut a=core::mem::ManuallyDrop::new(account());
#[cfg(NGL_record_borrow)]{a.length=Err(ProgramError::AccountBorrowFailed);a.bytes=Err(ProgramError::AccountBorrowFailed);}
#[cfg(NGL_record_rejected)]{a.length=Ok(kani::any());a.bytes=Err(ProgramError::InvalidAccountData);}
#[cfg(all(not(NGL_record_borrow),not(NGL_record_rejected)))]{let n:usize=kani::any();kani::assume(n<=NGL_CAP);let mut v=kani::vec::exact_vec::<u8,NGL_CAP>();v.truncate(n);a.length=Ok(n);a.bytes=Ok(v);}
let _=core::mem::ManuallyDrop::new(a.data());}

#[cfg(NGL_cap_1768)] const NGL_CAP:usize=1768;
#[cfg(NGL_cap_1880)] const NGL_CAP:usize=1880;
#[cfg(NGL_cap_384)] const NGL_CAP:usize=384;
#[cfg(NGL_cap_192)] const NGL_CAP:usize=192;
#[cfg(NGL_cap_768)] const NGL_CAP:usize=768;
#[cfg(NGL_cap_128)] const NGL_CAP:usize=128;
#[cfg(NGL_cap_256)] const NGL_CAP:usize=256;
#[cfg(NGL_cap_320)] const NGL_CAP:usize=320;
#[cfg(not(any(NGL_cap_1768,NGL_cap_1880,NGL_cap_384,NGL_cap_192,NGL_cap_768,NGL_cap_128,NGL_cap_256,NGL_cap_320)))] const NGL_CAP:usize=58295;
