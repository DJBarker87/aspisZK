macro_rules! NCL_eq {($left:expr,$right:expr)=>{assert!($left==$right)}}
use super::*;
#[kani::proof]
fn NCL_readonly_meta(){let s:bool=kani::any();let w:bool=kani::any();let e:bool=kani::any();let want=if s||w||e{Err(ProgramError::InvalidAccountData)}else{Ok(())};NCL_eq!(readonly_buffer_meta_ok(s,w,e),want);}
#[kani::proof]
fn NCL_readonly_meta_wrong(){NCL_eq!(readonly_buffer_meta_ok(true,false,false),Ok(()));}
#[kani::proof]
fn NCL_process_empty(){let p=Pubkey::new_from_array([0;32]);let split:u8=kani::any();kani::assume(split==10||split==11);NCL_eq!(process(&p,&[],&[3,split]),Err(ProgramError::InvalidInstructionData));}
#[kani::proof]
fn NCL_process_empty_wrong(){let p=Pubkey::new_from_array([0;32]);NCL_eq!(process(&p,&[],&[3,10]),Ok(()));}
#[kani::proof]
fn NCL_decode_short(){let bytes:[u8;8]=kani::any();let n:usize=kani::any();kani::assume(n<=8);assert!(matches!(decode_public_statement_box(&bytes[..n]),Err(ProgramError::InvalidAccountData)));}
#[kani::proof]
fn NCL_decode_short_wrong(){assert!(decode_public_statement_box(&[]).is_ok());}
