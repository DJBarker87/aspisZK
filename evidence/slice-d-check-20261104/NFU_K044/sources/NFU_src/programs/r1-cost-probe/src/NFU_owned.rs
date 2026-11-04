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
