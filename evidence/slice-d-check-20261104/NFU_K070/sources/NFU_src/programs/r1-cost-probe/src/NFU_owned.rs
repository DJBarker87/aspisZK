use super::*;
fn account()->OwnedAccount{OwnedAccount{key:Pubkey::new_from_array([0;32]),owner:Pubkey::new_from_array([0;32]),is_signer:kani::any(),is_writable:kani::any(),executable:kani::any(),length:Ok(0),bytes:Err(ProgramError::AccountBorrowFailed)}}
#[kani::proof]
fn readonly_buffer(){let a=core::mem::ManuallyDrop::new(account());let r=require_readonly_buffer(&a);let good=!(a.is_signer||a.is_writable||a.executable);let exact=if good{matches!(r,Ok(()))}else{matches!(r,Err(ProgramError::InvalidAccountData))};assert!(exact != cfg!(NFU_invert));}
#[kani::proof]
fn key_identity(){let a=core::mem::ManuallyDrop::new(account());assert!((core::ptr::eq(a.key(),&a.key)) != cfg!(NFU_invert));}
#[kani::proof]
fn owner_identity(){let a=core::mem::ManuallyDrop::new(account());assert!((core::ptr::eq(a.owner(),&a.owner)) != cfg!(NFU_invert));}

#[kani::proof] #[kani::unwind(3)]
fn stage1_empty(){let b:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);assert!(matches!(stage1(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage1_owned_empty(){let b:[u8;2]=kani::any();let n:usize=kani::any();kani::assume(n<=2);assert!(matches!(stage1_owned(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage2_empty(){let b:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);assert!(matches!(stage2(&Pubkey::new_from_array([0;32]),&[],&b[..n]),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}
#[kani::proof] #[kani::unwind(3)]
fn stage2_owned_empty(){let b:[u8;4]=kani::any();let n:usize=kani::any();kani::assume(n<=4);assert!(matches!(stage2_owned(&Pubkey::new_from_array([0;32]),&[],&b[..n],Ok(kani::any())),Err(ProgramError::InvalidInstructionData)) != cfg!(NFU_invert));}

// Source-shaped one iteration, retaining the original byte read and tail update.
fn zero_cut(mut remaining:&[u8])->(u8,&[u8],ProgramResult){
 if remaining.is_empty(){return(0,remaining,Ok(()));}
 if remaining[0]!=0{return(1,remaining,Err(ProgramError::AccountAlreadyInitialized));}
 remaining=&remaining[1..];(2,remaining,Ok(()))
}
#[kani::proof] #[kani::unwind(3)]
fn zero_full_step(){let b:[u8;4096]=kani::any();let start:usize=kani::any();let n:usize=kani::any();kani::assume(start<=4096&&n<=4096-start);let view=&b[start..start+n];let j:usize=kani::any();kani::assume(j<4096);let before=b[j];let(tag,rest,result)=zero_cut(view);let want=if n==0{0}else if b[start]!=0{1}else{2};let shift=if want==2{1}else{0};let exact=tag==want&&rest.len()==n-shift&&core::ptr::eq(rest.as_ptr(),view.as_ptr().wrapping_add(shift))&&b[j]==before&&if want==1{matches!(result,Err(ProgramError::AccountAlreadyInitialized))}else{matches!(result,Ok(()))};assert!(exact != cfg!(NFU_invert));}
